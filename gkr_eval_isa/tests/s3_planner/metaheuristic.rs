//! Test-only metaheuristic S3 ordering prototype.
//!
//! This module is research code for the joint random-key decoder described in
//! `.agents/specs/2026-06-25-metaheuristic-ordering-design.md`. It must stay out
//! of the production compiler path.

use super::forkset;
use crate::s3_gap::instance::{NodeKind, OracleInstance};

pub const ROOT_OUTPUT_INPUT_INDEX: u32 = u32::MAX;
const RECOVERY_BIAS_SCALE: f64 = 4.0;
const LOCAL_BIAS_STEP: f64 = 0.25;
const CACHE_FAMILY_QUOTA: usize = 64;
const TRACE_GUIDED_BIAS: f64 = 0.125;
const CACHE_PLATEAU_STEPS: usize = 4;
/// Maximum beam width (cap). The effective width scales with the eval budget — see
/// `beam_width_for_budget` and `BEAM_STATE_MIN_BUDGET`.
const OPTIMIZER_BEAM_WIDTH: usize = 8;
/// Empirical per-state convergence budget. A single greedy descent on the L0 corpus at
/// REAL_BUDGET stops improving within ~1000 evals — budget 2000 and 16000 reach the
/// SAME optimum at beam width 1. Below this per-state share the beam dilutes the best
/// trajectory and REGRESSES (width 8 @ budget 2000: 402→378); at or above it the surplus
/// budget funds breadth and the beam WINS (width 2 @ 2000: 403; width 8 @ 16000: 411).
/// The beam width is therefore `clamp(eval_budget / this, 1, OPTIMIZER_BEAM_WIDTH)`.
const BEAM_STATE_MIN_BUDGET: usize = 1_000;
/// H3: fixed per-iteration neighbor-batch cap, INDEPENDENT of the eval budget. The
/// root-insert move family is O(roots^2); without a fixed cap the first batch at
/// production scale (hundreds of roots) consumes the whole `eval_budget`, so the
/// local search degenerates to ~one greedy step. A constant cap funds many
/// iterations regardless of root count.
const NEIGHBOR_BATCH_CAP: usize = 128;
/// Simulated-annealing initial temperature, in read-traffic units. The optimizer's
/// uphill (Metropolis) acceptance escapes local optima the greedy descent stalls in;
/// the temperature cools linearly to 0 as the eval budget is spent (`sa_temperature`),
/// so the search anneals back to pure hill-climbing by the end of the budget.
const SA_INITIAL_TEMPERATURE: f64 = 4.0;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ValueClass {
    RamSource,
    Intermediate,
    CachedRootOutput,
    Other,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DemandSite {
    /// Index into `OracleInstance::roots`; root values may repeat, occurrences may not.
    pub root: u32,
    pub consumer: u32,
    pub input_index: u32,
    pub value: u32,
    pub class: ValueClass,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CachePrioritySite {
    pub structural_index: u32,
    pub root: u32,
    pub consumer: u32,
    pub input_index: u32,
    pub value: u32,
    pub class: ValueClass,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Genome {
    pub root_order_key: Vec<f64>,
    pub cache_priority: Vec<f64>,
}

impl Genome {
    pub fn neutral<T>(inst: &OracleInstance, sites: &[T]) -> Self {
        let denom = inst.roots.len().max(1) as f64;
        Self {
            root_order_key: (0..inst.roots.len()).map(|i| i as f64 / denom).collect(),
            cache_priority: vec![0.0; sites.len()],
        }
    }
}

pub fn classify_values(inst: &OracleInstance) -> Vec<ValueClass> {
    let mut consumers = vec![0u32; inst.nodes.len()];
    for node in &inst.nodes {
        for &child in &node.children {
            consumers[child as usize] += 1;
        }
    }
    for &root in &inst.roots {
        consumers[root as usize] += 1;
    }

    let mut is_root = vec![false; inst.nodes.len()];
    for &root in &inst.roots {
        is_root[root as usize] = true;
    }

    inst.nodes
        .iter()
        .enumerate()
        .map(|(idx, node)| {
            if node.real_dram && matches!(node.kind, NodeKind::Read) {
                ValueClass::RamSource
            } else if is_root[idx] && consumers[idx] > 1 {
                ValueClass::CachedRootOutput
            } else if consumers[idx] > 1
                && matches!(node.kind, NodeKind::Add | NodeKind::Mul | NodeKind::Special)
            {
                ValueClass::Intermediate
            } else {
                ValueClass::Other
            }
        })
        .collect()
}

pub fn enumerate_cache_priority_sites(inst: &OracleInstance) -> Vec<CachePrioritySite> {
    let classes = classify_values(inst);
    let mut sites = Vec::new();
    for (root_occurrence, &root_value) in inst.roots.iter().enumerate() {
        let root = root_occurrence as u32;
        let mut stack = vec![root_value];
        let mut seen = vec![false; inst.nodes.len()];
        while let Some(parent) = stack.pop() {
            if seen[parent as usize] {
                continue;
            }
            seen[parent as usize] = true;
            let node = &inst.nodes[parent as usize];
            for (input_index, &child) in node.children.iter().enumerate() {
                let class = classes[child as usize];
                if class != ValueClass::Other {
                    sites.push(CachePrioritySite {
                        structural_index: 0,
                        root,
                        consumer: parent,
                        input_index: input_index as u32,
                        value: child,
                        class,
                    });
                }
                stack.push(child);
            }
        }
        if matches!(
            classes[root_value as usize],
            ValueClass::RamSource | ValueClass::CachedRootOutput
        ) {
            sites.push(CachePrioritySite {
                structural_index: 0,
                root,
                consumer: root_value,
                input_index: ROOT_OUTPUT_INPUT_INDEX,
                value: root_value,
                class: ValueClass::CachedRootOutput,
            });
        }
    }
    sites.sort_by_key(|site| (site.root, site.consumer, site.input_index, site.value));
    sites.dedup_by_key(|site| (site.root, site.consumer, site.input_index, site.value));
    let mut structural_sites: Vec<(u32, u32, u32, ValueClass)> = sites
        .iter()
        .map(|site| (site.consumer, site.input_index, site.value, site.class))
        .collect();
    structural_sites.sort_unstable();
    structural_sites.dedup();
    for site in &mut sites {
        site.structural_index = structural_sites
            .binary_search(&(site.consumer, site.input_index, site.value, site.class))
            .expect("structural site must exist") as u32;
    }
    sites
}

pub fn enumerate_demand_sites(inst: &OracleInstance) -> Vec<DemandSite> {
    enumerate_cache_priority_sites(inst)
        .into_iter()
        .map(|site| DemandSite {
            root: site.root,
            consumer: site.consumer,
            input_index: site.input_index,
            value: site.value,
            class: site.class,
        })
        .collect()
}

pub fn decode_root_order(inst: &OracleInstance, genome: &Genome) -> Vec<u32> {
    decode_root_occurrence_order(inst, genome)
        .into_iter()
        .map(|root_occurrence| inst.roots[root_occurrence])
        .collect()
}

/// Per-occurrence sort tuple `(key, root_value, occurrence_index)` — the total
/// order the decoders break ties with. Comparing two tuples never panics on
/// finite keys; `assert_normalized_genome` (in scoring) guarantees finiteness,
/// and the decoder asserts the length up front.
fn root_sort_tuple(inst: &OracleInstance, genome: &Genome, occ: usize) -> (f64, u32, usize) {
    (genome.root_order_key[occ], inst.roots[occ], occ)
}

fn cmp_root_sort_tuple(a: &(f64, u32, usize), b: &(f64, u32, usize)) -> std::cmp::Ordering {
    a.0.partial_cmp(&b.0)
        .expect("root_order_key must be finite")
        .then(a.1.cmp(&b.1))
        .then(a.2.cmp(&b.2))
}

fn decode_root_occurrence_order(inst: &OracleInstance, genome: &Genome) -> Vec<usize> {
    assert_eq!(
        genome.root_order_key.len(),
        inst.roots.len(),
        "root_order_key length must match roots length"
    );
    let mut keyed: Vec<(f64, u32, usize)> = (0..inst.roots.len())
        .map(|idx| root_sort_tuple(inst, genome, idx))
        .collect();
    keyed.sort_by(cmp_root_sort_tuple);
    keyed
        .into_iter()
        .map(|(_, _, root_occurrence)| root_occurrence)
        .collect()
}

/// Per-unit "scheduling element" members: `units[u]` lists the occurrences of unit
/// `u` in canonical (gate-emission, i.e. ascending occurrence-index) order. Built
/// from `relation_units`' per-occurrence `unit_of` (ids are 0..n_units, contiguous,
/// assigned in encounter order). A 1-output relation / cache root is a singleton.
pub(crate) fn unit_members(unit_of: &[u32]) -> Vec<Vec<usize>> {
    let n_units = unit_of.iter().copied().max().map_or(0, |m| m as usize + 1);
    let mut units = vec![Vec::new(); n_units];
    for (occ, &u) in unit_of.iter().enumerate() {
        units[u as usize].push(occ);
    }
    units
}

/// True iff every unit's members form one contiguous run in `order` (used to test
/// whether an arbitrary — e.g. flat-optimized — occurrence order is atomicity-feasible).
pub(crate) fn order_keeps_units_contiguous(order: &[usize], units: &[Vec<usize>]) -> bool {
    let mut pos = vec![0usize; order.len()];
    for (i, &occ) in order.iter().enumerate() {
        pos[occ] = i;
    }
    units.iter().all(|members| {
        let (lo, hi) = members
            .iter()
            .fold((usize::MAX, 0usize), |(lo, hi), &occ| {
                (lo.min(pos[occ]), hi.max(pos[occ]))
            });
        members.is_empty() || hi - lo + 1 == members.len()
    })
}

/// The unit order a unit-keyed genome decodes to: unit indices sorted by their key,
/// ties broken by unit index for determinism. The genome's `root_order_key` holds
/// ONE key per unit here (length == number of units) — the unit is the scheduling
/// atom, so there is no per-member key and nothing to "keep together".
fn decode_unit_order(unit_key: &[f64]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..unit_key.len()).collect();
    order.sort_by(|&a, &b| {
        unit_key[a]
            .partial_cmp(&unit_key[b])
            .expect("unit_order_key must be finite")
            .then(a.cmp(&b))
    });
    order
}

/// Expand a unit-keyed genome to an occurrence order: order the units by key, then
/// concatenate each unit's members (canonical order). Empty `units` ⇒ the flat
/// per-occurrence decode (the genome is then per-occurrence, length == roots).
/// A unit is indivisible by construction, so every order this produces keeps each
/// relation's roots contiguous — atomicity is structural, not a re-projection.
pub(crate) fn decode_grouped_occurrence_order(
    inst: &OracleInstance,
    genome: &Genome,
    units: &[Vec<usize>],
) -> Vec<usize> {
    if units.is_empty() {
        return decode_root_occurrence_order(inst, genome);
    }
    assert_eq!(
        genome.root_order_key.len(),
        units.len(),
        "unit-keyed genome must have exactly one key per unit"
    );
    let mut order = Vec::with_capacity(inst.roots.len());
    for u in decode_unit_order(&genome.root_order_key) {
        order.extend_from_slice(&units[u]);
    }
    // Units must partition all occurrences exactly once — guard against a malformed
    // `units` silently dropping/duplicating roots (would corrupt scoring).
    assert_eq!(
        order.len(),
        inst.roots.len(),
        "units must cover every occurrence exactly once"
    );
    order
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CandidateScore {
    pub traffic: u64,
    pub instrs: u64,
    pub feasible: bool,
    pub order: Vec<u32>,
    pub admitted: u64,
    pub evicted: u64,
    pub dormant_sites: u64,
    pub admit_stats: AdmitStats,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AdmitStats {
    pub already_resident: u64,
    pub no_future_demand: u64,
    pub free_capacity: u64,
    pub pressure_rejected: u64,
    pub pressure_no_victim: u64,
    pub pressure_admitted: u64,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct CacheTrace {
    events: Vec<CacheTraceEvent>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum CacheTraceEvent {
    TrafficRead {
        root: u32,
        value: u32,
        site_idx: Option<usize>,
    },
    Admit {
        site_idx: usize,
        value: u32,
    },
    NoFutureDemand {
        site_idx: usize,
        value: u32,
    },
    PressureReject {
        site_idx: usize,
        value: u32,
    },
    PressureAdmit {
        site_idx: usize,
        value: u32,
    },
    Evict {
        site_idx: Option<usize>,
        victim: u32,
        victim_last_site: Option<usize>,
        victim_remaining: usize,
        cause: EvictCause,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EvictCause {
    Dead,
    PressureAdmit { admitted: u32 },
    Transient { width: usize },
}

/// Per-step action stream emitted by [`replay_plan`]. One `StepPlanRaw` is produced
/// per root occurrence (even for `real_dram`/infeasible roots, which contribute an
/// empty-event step with `resident_after == resident_before`). The stream is
/// node-id-keyed and behavior-preserving: it records state the scoring replay already
/// computes, so replaying `events` from `resident_before` reproduces `resident_after`.
///
/// `resident_before` is snapshotted AFTER `enforce_cone_fit` (so cone-fit transient
/// evictions are absorbed by it and are NOT events — spec §3); `resident_after` after
/// `finish_root`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct StepPlanRaw {
    pub(crate) resident_before: Vec<u32>,
    pub(crate) events: Vec<ReplayEventRaw>,
    pub(crate) resident_after: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ReplayEventRaw {
    Demand {
        consumer: u32,
        input_index: u32,
        value: u32,
        kind: DemandKindRaw,
    },
    Admit {
        value: u32,
    },
    Evict {
        value: u32,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DemandKindRaw {
    Resident,
    Reload,
    Recompute,
}

pub fn score_candidate(
    inst: &OracleInstance,
    sites: &[DemandSite],
    genome: &Genome,
) -> CandidateScore {
    score_candidate_internal(inst, sites, genome, false, &[]).0
}

/// Group-atomic scoring: the genome is unit-keyed and decoded via `units` so each
/// relation's roots stay contiguous (see [`decode_grouped_occurrence_order`]). An
/// empty `units` is identical to [`score_candidate`] (flat, per-occurrence genome).
pub(crate) fn score_candidate_grouped(
    inst: &OracleInstance,
    sites: &[DemandSite],
    genome: &Genome,
    units: &[Vec<usize>],
) -> CandidateScore {
    score_candidate_internal(inst, sites, genome, false, units).0
}

fn score_candidate_with_trace(
    inst: &OracleInstance,
    sites: &[DemandSite],
    genome: &Genome,
) -> (CandidateScore, CacheTrace) {
    score_candidate_internal(inst, sites, genome, true, &[])
}

pub(crate) fn score_candidate_internal(
    inst: &OracleInstance,
    sites: &[DemandSite],
    genome: &Genome,
    collect_trace: bool,
    units: &[Vec<usize>],
) -> (CandidateScore, CacheTrace) {
    assert_eq!(
        genome.cache_priority.len(),
        sites.len(),
        "cache_priority length must match demand-site count"
    );
    assert_normalized_genome(genome);

    let occurrence_order = decode_grouped_occurrence_order(inst, genome, units);
    let classes = classify_values(inst);
    let mut replay = Replay::new(
        inst,
        sites,
        genome,
        classes,
        &occurrence_order,
        collect_trace,
    );
    for &root_occurrence in &occurrence_order {
        replay.compute_root(root_occurrence);
        replay.finish_root(root_occurrence);
    }

    let trace = replay.trace.take().unwrap_or_default();
    let score = replay.into_score(&occurrence_order);
    (score, trace)
}

/// Behavior-preserving instrumentation: re-runs the SAME group-atomic scoring replay
/// over `genome` and additionally emits the per-step action stream. The returned
/// `CandidateScore` is identical to [`score_candidate_grouped`] for the same genome
/// (proven by the parity gate in `s3_gap_experiment.rs`); the second element is one
/// [`StepPlanRaw`] per root occurrence.
///
/// It OWNS the per-occurrence loop (rather than calling `compute_root`) so exactly one
/// step is pushed per occurrence even when `compute_root` would early-return
/// (`real_dram` / infeasible). The owned loop reproduces `compute_root` exactly:
/// `enforce_cone_fit` (guarded by feasibility, matching `compute_root`'s leading
/// guard) → `compute_root_body` (guarded) → `finish_root`. `resident_before` is
/// snapshotted between `enforce_cone_fit` and the body so cone-fit transient evicts are
/// absorbed into it and are NOT events; `resident_after` after `finish_root`.
pub(crate) fn replay_plan(
    inst: &OracleInstance,
    sites: &[DemandSite],
    genome: &Genome,
    units: &[Vec<usize>],
) -> (CandidateScore, Vec<StepPlanRaw>) {
    assert_eq!(
        genome.cache_priority.len(),
        sites.len(),
        "cache_priority length must match demand-site count"
    );
    assert_normalized_genome(genome);

    let occurrence_order = decode_grouped_occurrence_order(inst, genome, units);
    let classes = classify_values(inst);
    let mut replay = Replay::new(inst, sites, genome, classes, &occurrence_order, false);
    replay.step_events = Some(Vec::new());

    let mut steps = Vec::with_capacity(occurrence_order.len());
    for &occ in &occurrence_order {
        // Reproduce `compute_root` exactly (leading feasibility guard → cone-fit →
        // re-check → body), so scoring stays identical regardless of the early-outs.
        if replay.feasible {
            replay.enforce_cone_fit(occ);
        }
        let resident_before = replay.resident_snapshot();
        if replay.feasible {
            replay.compute_root_body(occ);
        }
        replay.finish_root(occ);
        let resident_after = replay.resident_snapshot();
        let events = std::mem::take(replay.step_events.as_mut().unwrap());
        steps.push(StepPlanRaw {
            resident_before,
            events,
            resident_after,
        });
    }

    let score = replay.into_score(&occurrence_order);
    (score, steps)
}

struct Replay<'a> {
    inst: &'a OracleInstance,
    sites: &'a [DemandSite],
    genome: &'a Genome,
    classes: Vec<ValueClass>,
    fork_info: forkset::ForkInfo,
    /// Sorted `cone(root)` per distinct root *value* (candidate-independent); empty
    /// slot = not a root value / not yet needed. Used by the cone-fit (C) gate to tell
    /// in-cone residents (shield) from outsiders (occupy budget during the cone).
    cone_of: Vec<Vec<u32>>,
    remaining_demands: Vec<usize>,
    remaining_site_demands: Vec<usize>,
    completed_root: Vec<bool>,
    resident: Vec<bool>,
    resident_keep: Vec<f64>,
    resident_keep_site: Vec<Option<usize>>,
    borrowed: Vec<u32>,
    resident_width: usize,
    traffic: u64,
    instrs: u64,
    feasible: bool,
    admitted: u64,
    evicted: u64,
    dormant_sites: u64,
    admit_stats: AdmitStats,
    trace: Option<CacheTrace>,
    /// Optional per-step event accumulator for [`replay_plan`]. `None` in normal
    /// scoring → every emit point is a no-op → the scoring path is byte-identical.
    /// `replay_plan` sets it to `Some(vec![])` and drains it once per occurrence.
    step_events: Option<Vec<ReplayEventRaw>>,
}

fn find_site_in(
    sites: &[DemandSite],
    root_occurrence: usize,
    consumer: u32,
    input_index: u32,
    value: u32,
) -> Option<usize> {
    sites.iter().position(|site| {
        site.root == root_occurrence as u32
            && site.consumer == consumer
            && site.input_index == input_index
            && site.value == value
    })
}

fn should_expand_policy_demand(
    inst: &OracleInstance,
    genome: &Genome,
    classes: &[ValueClass],
    completed_root: &[bool],
    value: u32,
    site_idx: usize,
) -> bool {
    match classes[value as usize] {
        ValueClass::RamSource => false,
        ValueClass::CachedRootOutput
            if completed_root[value as usize]
                && is_reloadable_value(inst, value)
                && choose_reload_policy(inst, genome, value, site_idx) =>
        {
            false
        }
        ValueClass::CachedRootOutput | ValueClass::Intermediate | ValueClass::Other => true,
    }
}

// Reload-vs-recompute for a reloadable CachedRootOutput. Returns true = RELOAD
// (re-read the backing, do NOT expand the producing sub-cone), false = RECOMPUTE.
//
// DESIGN (closes OQ3): the decision is a PER-SITE genome policy, NOT a residency-
// aware runtime computation, and that is deliberate on two grounds:
//   1. State-dependence is already expressed per site. A DemandSite is
//      (root_occurrence, consumer, input_index, value), so the SAME value demanded
//      in two different cones gets two DIFFERENT `recovery_bias` genes. Residency at
//      a demand point is a function of order + context, and the site encodes that
//      context — so the optimizer, tuning per-site recovery_bias, learns a
//      context- (hence residency-) adapted decision. (See the per-site divergence
//      test `recovery_policy_is_per_site_not_global`.)
//   2. The decision must be residency-BLIND to keep the liveness pre-count
//      (`remaining_demand_counts`, residency-free) consistent with the runtime
//      consumption (`consume_policy_demands`): both call this function, so it must
//      be a pure function of (value, site, genome). A residency-aware runtime
//      decision would expand cones the pre-count never counted → counter underflow.
//      (This is the same shielding-blind hazard that the inner_dp two-phase fix
//      resolved — eviction here is genome-keep-score driven, NOT Belady, so there
//      is no next-use optimality to preserve, only liveness consistency.)
// `recompute_traffic_for` is therefore the zero-bias PRIOR (an empty-cache full-cone
// estimate); recovery_bias shifts it per site and the optimizer corrects it.
fn choose_reload_policy(
    inst: &OracleInstance,
    genome: &Genome,
    value: u32,
    site_idx: usize,
) -> bool {
    let reload_cost = inst.nodes[value as usize].width as f64;
    let recompute_cost = recompute_traffic_for(inst, value) as f64;
    (-reload_cost + RECOVERY_BIAS_SCALE * genome.cache_priority[site_idx]) >= -recompute_cost
}

fn is_reloadable_value(inst: &OracleInstance, value: u32) -> bool {
    inst.reloadable_values.binary_search(&value).is_ok()
}

fn recompute_traffic_for(inst: &OracleInstance, value: u32) -> u64 {
    let mut seen = vec![false; inst.nodes.len()];
    let mut stack = vec![value];
    let mut traffic = 0u64;
    while let Some(id) = stack.pop() {
        if seen[id as usize] {
            continue;
        }
        seen[id as usize] = true;
        let node = &inst.nodes[id as usize];
        if node.real_dram {
            traffic += node.width as u64;
        }
        for &child in &node.children {
            stack.push(child);
        }
    }
    traffic
}

/// DAG-computable **ceiling**: the maximum reads when NOTHING is cached or shared —
/// every demand recomputes its value from base reads (the budget→0 limit). Pure graph
/// traversal (no search), so it is a hard upper bound: any feasible schedule reuses at
/// least as much, hence `floor ≤ optimizer_traffic ≤ no_cache_ceiling`. A scored result
/// above this means the scorer/search is broken, not merely sub-optimal.
pub(crate) fn no_cache_ceiling(inst: &OracleInstance, sites: &[DemandSite]) -> u64 {
    sites
        .iter()
        .map(|s| recompute_traffic_for(inst, s.value))
        .sum()
}

impl<'a> Replay<'a> {
    fn new(
        inst: &'a OracleInstance,
        sites: &'a [DemandSite],
        genome: &'a Genome,
        classes: Vec<ValueClass>,
        order: &[usize],
        collect_trace: bool,
    ) -> Self {
        let (remaining_demands, remaining_site_demands) =
            Self::remaining_demand_counts(inst, sites, genome, order);
        let mut cone_of: Vec<Vec<u32>> = vec![Vec::new(); inst.nodes.len()];
        for &root_occurrence in order {
            let rv = inst.roots[root_occurrence] as usize;
            if cone_of[rv].is_empty() {
                cone_of[rv] = forkset::cone(inst, rv as u32); // sorted, always ≥1 (the root)
            }
        }
        Self {
            inst,
            sites,
            genome,
            classes,
            fork_info: forkset::analyze(inst),
            cone_of,
            remaining_demands,
            remaining_site_demands,
            completed_root: vec![false; inst.nodes.len()],
            resident: vec![false; inst.nodes.len()],
            resident_keep: vec![0.0; inst.nodes.len()],
            resident_keep_site: vec![None; inst.nodes.len()],
            borrowed: vec![0; inst.nodes.len()],
            resident_width: 0,
            traffic: 0,
            instrs: 0,
            feasible: true,
            admitted: 0,
            evicted: 0,
            dormant_sites: 0,
            admit_stats: AdmitStats::default(),
            trace: collect_trace.then(CacheTrace::default),
            step_events: None,
        }
    }

    fn remaining_demand_counts(
        inst: &OracleInstance,
        sites: &[DemandSite],
        genome: &Genome,
        order: &[usize],
    ) -> (Vec<usize>, Vec<usize>) {
        let mut counts = vec![0usize; inst.nodes.len()];
        let mut site_counts = vec![0usize; sites.len()];
        let classes = classify_values(inst);
        let mut completed_root = vec![false; inst.nodes.len()];
        for &root_occurrence in order {
            let root_value = inst.roots[root_occurrence];
            Self::add_policy_demands(
                inst,
                sites,
                genome,
                &classes,
                &completed_root,
                root_occurrence,
                root_value,
                &mut counts,
                &mut site_counts,
            );
            if inst.nodes[root_value as usize].real_dram {
                if let Some(site_idx) = find_site_in(
                    sites,
                    root_occurrence,
                    root_value,
                    ROOT_OUTPUT_INPUT_INDEX,
                    root_value,
                ) {
                    counts[root_value as usize] += 1;
                    site_counts[site_idx] += 1;
                }
            }
            completed_root[root_value as usize] = true;
        }
        (counts, site_counts)
    }

    fn add_policy_demands(
        inst: &OracleInstance,
        sites: &[DemandSite],
        genome: &Genome,
        classes: &[ValueClass],
        completed_root: &[bool],
        root_occurrence: usize,
        node_id: u32,
        counts: &mut [usize],
        site_counts: &mut [usize],
    ) {
        for (input_index, &child) in inst.nodes[node_id as usize].children.iter().enumerate() {
            if let Some(site_idx) =
                find_site_in(sites, root_occurrence, node_id, input_index as u32, child)
            {
                counts[child as usize] += 1;
                site_counts[site_idx] += 1;
                if should_expand_policy_demand(
                    inst,
                    genome,
                    classes,
                    completed_root,
                    child,
                    site_idx,
                ) {
                    Self::add_policy_demands(
                        inst,
                        sites,
                        genome,
                        classes,
                        completed_root,
                        root_occurrence,
                        child,
                        counts,
                        site_counts,
                    );
                }
            } else {
                Self::add_policy_demands(
                    inst,
                    sites,
                    genome,
                    classes,
                    completed_root,
                    root_occurrence,
                    child,
                    counts,
                    site_counts,
                );
            }
        }
    }

    fn compute_node(&mut self, root_occurrence: usize, node_id: u32) {
        if !self.feasible {
            return;
        }
        if self.resident[node_id as usize] {
            self.dormant_sites += self.count_subtree_sites(root_occurrence, node_id);
            self.consume_policy_demands(root_occurrence, node_id);
            return;
        }
        if self.inst.nodes[node_id as usize].real_dram {
            self.traffic += self.inst.nodes[node_id as usize].width as u64;
            self.trace_event(CacheTraceEvent::TrafficRead {
                root: self.inst.roots[root_occurrence],
                value: node_id,
                site_idx: None,
            });
            return;
        }

        let children = self.inst.nodes[node_id as usize].children.clone();
        for (input_index, child) in children.into_iter().enumerate() {
            if let Some(site_idx) =
                self.find_site(root_occurrence, node_id, input_index as u32, child)
            {
                self.consume_site(site_idx);
                if self.satisfy_demand(root_occurrence, child, site_idx) {
                    self.borrow_value(child);
                    self.release_value(child);
                }
            } else {
                self.compute_node(root_occurrence, child);
            }
        }

        // Streaming model: computing an instr node leaves its result in the separate
        // accumulator register (not the cell budget); operands stream in. The only cell
        // pressure — the single-accumulator spill on nested folds — is charged once per
        // cone by `enforce_cone_fit`, not per node here.
        if is_instr_node(self.inst.nodes[node_id as usize].kind) {
            self.instrs += 1;
        }
    }

    fn compute_root(&mut self, root_occurrence: usize) {
        if !self.feasible {
            return;
        }
        self.enforce_cone_fit(root_occurrence);
        if !self.feasible {
            return;
        }
        self.compute_root_body(root_occurrence);
    }

    /// Everything in `compute_root` AFTER the `enforce_cone_fit` + feasibility re-check.
    /// Split out so `replay_plan` can own the per-occurrence loop and snapshot
    /// `resident_before` between `enforce_cone_fit` and this body — keeping exactly one
    /// `StepPlanRaw` per occurrence regardless of the `real_dram`/infeasible early-outs.
    /// Behavior-identical to the inline body it replaced (the scoring loop is unchanged).
    fn compute_root_body(&mut self, root_occurrence: usize) {
        let root = self.inst.roots[root_occurrence];
        let node = &self.inst.nodes[root as usize];
        if node.real_dram {
            if !self.resident[root as usize] {
                self.traffic += node.width as u64;
                self.trace_event(CacheTraceEvent::TrafficRead {
                    root,
                    value: root,
                    site_idx: None,
                });
            }
            return;
        }
        self.compute_node(root_occurrence, root);
    }

    /// IDs of the currently resident values, ascending. Snapshotted by `replay_plan`
    /// to bound each step's event stream (`resident_before`/`resident_after`).
    fn resident_snapshot(&self) -> Vec<u32> {
        (0..self.resident.len() as u32)
            .filter(|&i| self.resident[i as usize])
            .collect()
    }

    /// Shared `CandidateScore` assembly used by both `score_candidate_internal` and
    /// `replay_plan`, so the two paths produce byte-identical scores (the parity gate).
    /// `occurrence_order` is the decoded per-occurrence order (root-occurrence indices).
    fn into_score(&self, occurrence_order: &[usize]) -> CandidateScore {
        CandidateScore {
            traffic: self.traffic,
            instrs: self.instrs,
            feasible: self.feasible,
            order: occurrence_order
                .iter()
                .map(|&root_occurrence| self.inst.roots[root_occurrence])
                .collect(),
            admitted: self.admitted,
            evicted: self.evicted,
            dormant_sites: self.dormant_sites,
            admit_stats: self.admit_stats,
        }
    }

    fn finish_root(&mut self, root_occurrence: usize) {
        let root = self.inst.roots[root_occurrence];
        if let Some(site_idx) = self.find_site(root_occurrence, root, ROOT_OUTPUT_INPUT_INDEX, root)
        {
            if self.inst.nodes[root as usize].real_dram {
                self.consume_site(site_idx);
            }
            if self.resident[root as usize] {
                self.stamp_keep(root, site_idx);
            } else {
                self.maybe_admit(root, site_idx);
            }
        }
        self.completed_root[root as usize] = true;
    }

    fn satisfy_demand(&mut self, root_occurrence: usize, value: u32, site_idx: usize) -> bool {
        if self.resident[value as usize] {
            self.emit_demand(site_idx, DemandKindRaw::Resident);
            self.stamp_keep(value, site_idx);
            self.dormant_sites += self.count_subtree_sites(root_occurrence, value);
            self.consume_policy_demands(root_occurrence, value);
            return true;
        }

        match self.classes[value as usize] {
            ValueClass::RamSource => {
                self.emit_demand(site_idx, DemandKindRaw::Reload);
                self.traffic += self.inst.nodes[value as usize].width as u64;
                self.trace_event(CacheTraceEvent::TrafficRead {
                    root: self.inst.roots[root_occurrence],
                    value,
                    site_idx: Some(site_idx),
                });
            }
            ValueClass::Intermediate => {
                self.emit_demand(site_idx, DemandKindRaw::Recompute);
                self.compute_node(root_occurrence, value);
            }
            ValueClass::CachedRootOutput => {
                if self.completed_root[value as usize]
                    && self.is_reloadable(value)
                    && self.choose_reload(value, site_idx)
                {
                    self.emit_demand(site_idx, DemandKindRaw::Reload);
                    self.traffic += self.inst.nodes[value as usize].width as u64;
                    self.trace_event(CacheTraceEvent::TrafficRead {
                        root: self.inst.roots[root_occurrence],
                        value,
                        site_idx: Some(site_idx),
                    });
                    self.consume_policy_demands(root_occurrence, value);
                } else {
                    self.emit_demand(site_idx, DemandKindRaw::Recompute);
                    self.compute_node(root_occurrence, value);
                }
            }
            ValueClass::Other => {
                self.emit_demand(site_idx, DemandKindRaw::Recompute);
                self.compute_node(root_occurrence, value);
            }
        }

        self.maybe_admit(value, site_idx);
        self.resident[value as usize]
    }

    /// Emit one `Demand` event for the resolution decided in `satisfy_demand` (no-op
    /// when not capturing). Demand identity comes from `sites[site_idx]` (consumer/
    /// input_index/value), per spec — they are not free locals here. The root-output
    /// pseudo-site (`input_index == ROOT_OUTPUT_INPUT_INDEX`) is skipped: it is not a
    /// consumer demand and the integrity test asserts no Demand carries it.
    fn emit_demand(&mut self, site_idx: usize, kind: DemandKindRaw) {
        let site = &self.sites[site_idx];
        if site.input_index == ROOT_OUTPUT_INPUT_INDEX {
            return;
        }
        let event = ReplayEventRaw::Demand {
            consumer: site.consumer,
            input_index: site.input_index,
            value: site.value,
            kind,
        };
        if let Some(events) = &mut self.step_events {
            events.push(event);
        }
    }

    fn choose_reload(&self, value: u32, site_idx: usize) -> bool {
        choose_reload_policy(self.inst, self.genome, value, site_idx)
    }

    fn maybe_admit(&mut self, value: u32, site_idx: usize) {
        if self.resident[value as usize] {
            self.admit_stats.already_resident += 1;
            return;
        }
        if !self.has_future_demand(value, site_idx) {
            self.admit_stats.no_future_demand += 1;
            self.trace_event(CacheTraceEvent::NoFutureDemand { site_idx, value });
            return;
        }

        self.evict_dead_residents(site_idx);

        let width = self.inst.nodes[value as usize].width as usize;
        if self.used_width() + width <= self.inst.budget {
            self.admit_stats.free_capacity += 1;
            self.admit_value(value, site_idx);
            return;
        }

        if self.genome.cache_priority[site_idx] <= 0.0 {
            self.admit_stats.pressure_rejected += 1;
            self.trace_event(CacheTraceEvent::PressureReject { site_idx, value });
            return;
        }

        while self.used_width() + width > self.inst.budget {
            let Some(victim) = self.lowest_keep_resident() else {
                self.admit_stats.pressure_no_victim += 1;
                return;
            };
            let victim_last_site = self.resident_keep_site[victim];
            self.resident[victim] = false;
            self.resident_width -= self.inst.nodes[victim].width as usize;
            self.evicted += 1;
            self.trace_event(CacheTraceEvent::Evict {
                site_idx: Some(site_idx),
                victim: victim as u32,
                victim_last_site,
                victim_remaining: self.remaining_demands[victim],
                cause: EvictCause::PressureAdmit { admitted: value },
            });
            // Post-snapshot eviction (cause PressureAdmit) → an event.
            if let Some(events) = &mut self.step_events {
                events.push(ReplayEventRaw::Evict {
                    value: victim as u32,
                });
            }
        }

        if self.used_width() + width <= self.inst.budget {
            self.admit_stats.pressure_admitted += 1;
            self.trace_event(CacheTraceEvent::PressureAdmit { site_idx, value });
            self.admit_value(value, site_idx);
        }
    }

    fn admit_value(&mut self, value: u32, site_idx: usize) {
        self.resident[value as usize] = true;
        self.resident_width += self.inst.nodes[value as usize].width as usize;
        self.stamp_keep(value, site_idx);
        self.admitted += 1;
        self.trace_event(CacheTraceEvent::Admit { site_idx, value });
        if let Some(events) = &mut self.step_events {
            events.push(ReplayEventRaw::Admit { value });
        }
    }

    // KEEP REDUCTION (M2). `keep_after_use_bias` is a PER-SITE gene, but a value has a
    // single residency, so its keep priority is stored as ONE scalar in
    // `resident_keep[value]`, overwritten by whichever site last stamps it — on
    // admission AND on every reuse (`finish_root`, `satisfy_demand`, `admit_value`).
    // The eviction comparators (`lowest_keep_resident`/`lowest_keep_outsider`) read
    // only that scalar, so the EFFECTIVE per-value keep priority is the LAST-stamping
    // site's gene. This is an explicit last-stamp reduction over the per-site genes.
    //
    // Consequence: the priority couples to the decoded root order (which site stamps
    // last shifts with the order) — a known divergence from design.md:89, which
    // specified a value-keyed `vec![0.0; nodes.len()]`. It is NOT a correctness bug:
    // eviction stays a total order via the id tie-break, and the optimizer tunes
    // whichever site stamps last. A clean unit pinning test is impractical (on small
    // synthetic instances the scorer caches the leaf Reads, not the folds, so fold
    // keep genes are inert); the lever's aggregate effect is covered by the corpus
    // read-floor / all-fit invariants. If M6 shows the keep lever underperforms,
    // promoting it to a value-keyed gene (one per node) is the documented next step.
    fn stamp_keep(&mut self, value: u32, site_idx: usize) {
        self.resident_keep[value as usize] = self.genome.cache_priority[site_idx];
        self.resident_keep_site[value as usize] = Some(site_idx);
    }

    fn evict_dead_residents(&mut self, site_idx: usize) {
        for value in 0..self.resident.len() {
            if self.resident[value]
                && self.borrowed[value] == 0
                && !self.has_future_demand(value as u32, site_idx)
            {
                let victim_last_site = self.resident_keep_site[value];
                self.resident[value] = false;
                self.resident_width -= self.inst.nodes[value].width as usize;
                self.evicted += 1;
                self.trace_event(CacheTraceEvent::Evict {
                    site_idx: Some(site_idx),
                    victim: value as u32,
                    victim_last_site,
                    victim_remaining: self.remaining_demands[value],
                    cause: EvictCause::Dead,
                });
                // Post-snapshot eviction (cause Dead) → an event.
                if let Some(events) = &mut self.step_events {
                    events.push(ReplayEventRaw::Evict {
                        value: value as u32,
                    });
                }
            }
        }
    }

    fn has_future_demand(&self, value: u32, site_idx: usize) -> bool {
        let _ = site_idx;
        self.remaining_demands[value as usize] > 0
    }

    fn consume_site(&mut self, site_idx: usize) {
        if self.remaining_site_demands[site_idx] == 0 {
            return;
        }
        self.remaining_site_demands[site_idx] -= 1;
        let value = self.sites[site_idx].value as usize;
        debug_assert!(self.remaining_demands[value] > 0);
        self.remaining_demands[value] -= 1;
    }

    fn consume_policy_demands(&mut self, root_occurrence: usize, node_id: u32) {
        let completed_root = self.completed_root.clone();
        self.consume_policy_demands_with_completed(root_occurrence, node_id, &completed_root);
    }

    fn consume_policy_demands_with_completed(
        &mut self,
        root_occurrence: usize,
        node_id: u32,
        completed_root: &[bool],
    ) {
        let children = self.inst.nodes[node_id as usize].children.clone();
        for (input_index, child) in children.into_iter().enumerate() {
            if let Some(site_idx) =
                self.find_site(root_occurrence, node_id, input_index as u32, child)
            {
                self.consume_site(site_idx);
                if self.should_expand_policy_demand_with_completed(child, site_idx, completed_root)
                {
                    self.consume_policy_demands_with_completed(
                        root_occurrence,
                        child,
                        completed_root,
                    );
                }
            } else {
                self.consume_policy_demands_with_completed(root_occurrence, child, completed_root);
            }
        }
    }

    /// (C) cone-fit: computing `root`'s cone needs its single-accumulator spill peak
    /// (`fork_info.peak[root]`) of cells on top of the resident values that are
    /// OUTSIDERS to this cone. In-cone residents shield their subtrees and are folded
    /// into the conservative static peak (matching `inner_dp`'s (C) check), so they are
    /// not charged here. Evict the lowest-keep unborrowed outsider until it fits; if the
    /// peak alone exceeds the budget, or no outsider can be freed, the cone cannot be
    /// scheduled.
    fn enforce_cone_fit(&mut self, root_occurrence: usize) {
        let root = self.inst.roots[root_occurrence];
        let cone_peak = self.fork_info.peak[root as usize] as usize;
        if cone_peak > self.inst.budget {
            self.feasible = false;
            return;
        }
        loop {
            if self.outsider_resident_width(root) + cone_peak <= self.inst.budget {
                return;
            }
            let Some(victim) = self.lowest_keep_outsider(root) else {
                self.feasible = false;
                return;
            };
            let victim_last_site = self.resident_keep_site[victim];
            self.resident[victim] = false;
            self.resident_width -= self.inst.nodes[victim].width as usize;
            self.evicted += 1;
            self.trace_event(CacheTraceEvent::Evict {
                site_idx: None,
                victim: victim as u32,
                victim_last_site,
                victim_remaining: self.remaining_demands[victim],
                cause: EvictCause::Transient { width: cone_peak },
            });
        }
    }

    fn is_outsider(&self, root: u32, value: usize) -> bool {
        self.cone_of[root as usize].binary_search(&(value as u32)).is_err()
    }

    fn outsider_resident_width(&self, root: u32) -> usize {
        (0..self.resident.len())
            .filter(|&v| self.resident[v] && self.is_outsider(root, v))
            .map(|v| self.inst.nodes[v].width as usize)
            .sum()
    }

    fn lowest_keep_outsider(&self, root: u32) -> Option<usize> {
        self.resident
            .iter()
            .enumerate()
            .filter(|&(idx, &is_resident)| {
                is_resident && self.borrowed[idx] == 0 && self.is_outsider(root, idx)
            })
            .min_by(|&(a, _), &(b, _)| {
                self.resident_keep[a]
                    .partial_cmp(&self.resident_keep[b])
                    .expect("resident keep score must be finite")
                    .then(a.cmp(&b))
            })
            .map(|(idx, _)| idx)
    }

    fn used_width(&self) -> usize {
        self.resident_width
    }

    fn borrow_value(&mut self, value: u32) {
        self.borrowed[value as usize] += 1;
    }

    fn release_value(&mut self, value: u32) {
        let count = &mut self.borrowed[value as usize];
        debug_assert!(*count > 0, "release without borrow for value {value}");
        *count = count.saturating_sub(1);
    }

    fn lowest_keep_resident(&self) -> Option<usize> {
        self.resident
            .iter()
            .enumerate()
            .filter(|&(idx, &is_resident)| is_resident && self.borrowed[idx] == 0)
            .min_by(|&(a, _), &(b, _)| {
                self.resident_keep[a]
                    .partial_cmp(&self.resident_keep[b])
                    .expect("resident keep score must be finite")
                    .then(a.cmp(&b))
            })
            .map(|(idx, _)| idx)
    }

    fn find_site(
        &self,
        root_occurrence: usize,
        consumer: u32,
        input_index: u32,
        value: u32,
    ) -> Option<usize> {
        find_site_in(self.sites, root_occurrence, consumer, input_index, value)
    }

    fn is_reloadable(&self, value: u32) -> bool {
        is_reloadable_value(self.inst, value)
    }

    fn should_expand_policy_demand_with_completed(
        &self,
        value: u32,
        site_idx: usize,
        completed_root: &[bool],
    ) -> bool {
        should_expand_policy_demand(
            self.inst,
            self.genome,
            &self.classes,
            completed_root,
            value,
            site_idx,
        )
    }

    fn count_subtree_sites(&self, root_occurrence: usize, node_id: u32) -> u64 {
        let mut seen = vec![false; self.inst.nodes.len()];
        let mut stack = vec![node_id];
        let mut count = 0u64;
        while let Some(id) = stack.pop() {
            if seen[id as usize] {
                continue;
            }
            seen[id as usize] = true;
            for (input_index, &child) in self.inst.nodes[id as usize].children.iter().enumerate() {
                if self
                    .find_site(root_occurrence, id, input_index as u32, child)
                    .is_some()
                {
                    count += 1;
                }
                stack.push(child);
            }
        }
        count
    }

    fn trace_event(&mut self, event: CacheTraceEvent) {
        if let Some(trace) = &mut self.trace {
            trace.events.push(event);
        }
    }

    fn recompute_traffic(&self, value: u32) -> u64 {
        recompute_traffic_for(self.inst, value)
    }
}

fn is_instr_node(kind: NodeKind) -> bool {
    matches!(kind, NodeKind::Add | NodeKind::Mul | NodeKind::Special)
}

fn assert_normalized_genome(genome: &Genome) {
    for &key in &genome.root_order_key {
        assert!(
            key.is_finite() && (0.0..=1.0).contains(&key),
            "root_order_key must be finite and in [0, 1], got {key}"
        );
    }
    for &gene in &genome.cache_priority {
        assert!(
            gene.is_finite() && (-1.0..=1.0).contains(&gene),
            "bias genes must be finite and in [-1, 1], got {gene}"
        );
    }
}

fn clamp_bias(value: f64) -> f64 {
    value.clamp(-1.0, 1.0)
}

pub fn perturb_one_gene(genome: &Genome, index: usize, delta: f64) -> Genome {
    let mut out = genome.clone();
    if index < out.root_order_key.len() {
        out.root_order_key[index] = (out.root_order_key[index] + delta).clamp(0.0, 1.0);
        return out;
    }
    let index = index - out.root_order_key.len();
    if index < out.cache_priority.len() {
        out.cache_priority[index] = clamp_bias(out.cache_priority[index] + delta);
        return out;
    }
    panic!("gene index {index} out of range");
}

// Flat-path re-export so consumers reach the optimizer driver as `metaheuristic::<item>` instead of
// coupling to the `tests` submodule. `OptimizerResult` stays internal to `tests` (used only there).
#[cfg(test)]
pub(crate) use tests::{
    optimize_from_population_grouped, project_genome_to_units, seeded_smoke_population,
};

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::s3_gap::instance::{OracleInstance, OracleNode};

    fn n(id: u32, kind: NodeKind, width: u8, real_dram: bool, children: Vec<u32>) -> OracleNode {
        OracleNode {
            id,
            kind,
            width,
            real_dram,
            children,
        }
    }

    fn candidate_score(traffic: u64, instrs: u64) -> CandidateScore {
        CandidateScore {
            traffic,
            instrs,
            feasible: true,
            order: Vec::new(),
            admitted: 0,
            evicted: 0,
            dormant_sites: 0,
            admit_stats: AdmitStats::default(),
        }
    }

    fn scored_test_candidate(
        index: usize,
        score: CandidateScore,
        family: MoveFamily,
    ) -> ScoredGenome {
        ScoredGenome {
            index,
            genome: Genome {
                root_order_key: vec![index as f64],
                cache_priority: Vec::new(),
            },
            score,
            family: Some(family),
        }
    }

    fn trace_guided_cache_fixture() -> OracleInstance {
        OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![3, 4, 5, 6, 7, 8, 9],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Read, 1, true, vec![]),
                n(3, NodeKind::Add, 1, false, vec![0]),
                n(4, NodeKind::Add, 1, false, vec![1]),
                n(5, NodeKind::Add, 1, false, vec![0]),
                n(6, NodeKind::Add, 1, false, vec![2]),
                n(7, NodeKind::Add, 1, false, vec![2]),
                n(8, NodeKind::Add, 1, false, vec![1]),
                n(9, NodeKind::Add, 1, false, vec![0]),
            ],
        }
    }

    fn trace_guided_cache_genome(inst: &OracleInstance, sites: &[DemandSite]) -> Genome {
        let mut genome = Genome::neutral(inst, sites);
        for (idx, site) in sites.iter().enumerate() {
            genome.cache_priority[idx] = match site.value {
                1 => -1.0,
                2 => 1.0,
                _ => 0.0,
            };
        }
        genome
    }

    fn swap_optimizer_fixture() -> OracleInstance {
        OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![2, 3, 4, 5],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0]),
                n(3, NodeKind::Add, 1, false, vec![1]),
                n(4, NodeKind::Add, 1, false, vec![0]),
                n(5, NodeKind::Add, 1, false, vec![1]),
            ],
        }
    }

    #[test]
    fn classifies_ram_sources_intermediates_and_cached_root_outputs() {
        let inst = OracleInstance {
            budget: 4,
            reloadable_values: vec![],
            roots: vec![2, 4, 5],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0, 1]),
                n(3, NodeKind::Mul, 1, false, vec![0, 1]),
                n(4, NodeKind::Add, 1, false, vec![2, 3]),
                n(5, NodeKind::Add, 1, false, vec![3]),
            ],
        };

        let classes = classify_values(&inst);

        assert_eq!(classes[0], ValueClass::RamSource);
        assert_eq!(classes[1], ValueClass::RamSource);
        assert_eq!(classes[2], ValueClass::CachedRootOutput);
        assert_eq!(classes[3], ValueClass::Intermediate);
        assert_eq!(classes[4], ValueClass::Other);
    }

    #[test]
    fn genome_neutral_uses_order_and_cache_priority_only() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![1, 2],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Add, 1, false, vec![0]),
                n(2, NodeKind::Add, 1, false, vec![0]),
            ],
        };
        let sites = enumerate_cache_priority_sites(&inst);
        let genome = Genome::neutral(&inst, &sites);

        assert_eq!(genome.root_order_key.len(), inst.roots.len());
        assert_eq!(genome.cache_priority.len(), sites.len());
    }

    #[test]
    fn cache_priority_sites_include_reused_root_output_site() {
        let inst = OracleInstance {
            budget: 0,
            reloadable_values: vec![2],
            roots: vec![2, 4],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0, 1]),
                n(3, NodeKind::Read, 1, true, vec![]),
                n(4, NodeKind::Add, 1, false, vec![2, 3]),
            ],
        };

        let sites = enumerate_cache_priority_sites(&inst);

        assert!(sites.iter().any(|site| {
            site.value == 2 && site.input_index == ROOT_OUTPUT_INPUT_INDEX
        }));
    }

    #[test]
    fn replay_charges_direct_read_root() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![0],
            nodes: vec![n(0, NodeKind::Read, 1, true, vec![])],
        };
        let sites = enumerate_demand_sites(&inst);
        let genome = Genome::neutral(&inst, &sites);

        let score = score_candidate(&inst, &sites, &genome);

        assert_eq!(score.traffic, 1);
        assert!(score.feasible);
    }

    #[test]
    fn direct_read_root_can_be_cached_for_later_demand() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![0, 1],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Add, 1, false, vec![0]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let genome = Genome::neutral(&inst, &sites);

        let score = score_candidate(&inst, &sites, &genome);

        assert_eq!(score.traffic, 1);
        assert_eq!(score.admit_stats.free_capacity, 1);
        assert!(score.feasible);
    }

    #[test]
    fn no_future_filter_tracks_repeated_root_occurrences() {
        let inst = OracleInstance {
            budget: 6,
            reloadable_values: vec![],
            roots: vec![1, 3, 1],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Add, 1, false, vec![0]),
                n(2, NodeKind::Read, 1, true, vec![]),
                n(3, NodeKind::Add, 1, false, vec![2]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let genome = Genome::neutral(&inst, &sites);

        let score = score_candidate(&inst, &sites, &genome);

        assert_eq!(score.traffic, 2);
        assert!(score.feasible);
    }

    #[test]
    fn repeated_root_occurrences_get_distinct_demand_sites() {
        let inst = OracleInstance {
            budget: 6,
            reloadable_values: vec![],
            roots: vec![1, 3, 1],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Add, 1, false, vec![0]),
                n(2, NodeKind::Read, 1, true, vec![]),
                n(3, NodeKind::Add, 1, false, vec![2]),
            ],
        };

        let sites = enumerate_demand_sites(&inst);
        let repeated_source_sites = sites.iter().filter(|site| site.value == 0).count();

        assert_eq!(repeated_source_sites, 2);
    }

    #[test]
    fn future_reload_does_not_keep_recomputed_inputs_alive() {
        let inst = OracleInstance {
            budget: 8,
            reloadable_values: vec![2],
            roots: vec![2, 3],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0, 1]),
                n(3, NodeKind::Add, 1, false, vec![2]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let mut genome = Genome::neutral(&inst, &sites);
        for (idx, site) in sites.iter().enumerate() {
            if site.value == 2 {
                genome.cache_priority[idx] = 1.0;
                genome.cache_priority[idx] = 1.0;
            }
        }

        let score = score_candidate(&inst, &sites, &genome);

        assert_eq!(score.traffic, 2);
        assert_eq!(score.admitted, 1);
    }

    #[test]
    fn enumerates_demand_sites_by_static_consumer_edge() {
        let inst = OracleInstance {
            budget: 4,
            reloadable_values: vec![],
            roots: vec![2, 4, 5],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0, 1]),
                n(3, NodeKind::Mul, 1, false, vec![0, 1]),
                n(4, NodeKind::Add, 1, false, vec![2, 3]),
                n(5, NodeKind::Add, 1, false, vec![3]),
            ],
        };

        let sites = enumerate_demand_sites(&inst);

        assert!(sites.contains(&DemandSite {
            root: 0,
            consumer: 2,
            input_index: 0,
            value: 0,
            class: ValueClass::RamSource,
        }));
        assert!(sites.contains(&DemandSite {
            root: 1,
            consumer: 4,
            input_index: 0,
            value: 2,
            class: ValueClass::CachedRootOutput,
        }));
        assert!(sites.contains(&DemandSite {
            root: 1,
            consumer: 4,
            input_index: 1,
            value: 3,
            class: ValueClass::Intermediate,
        }));
    }

    #[test]
    fn enumerates_root_output_completion_site_for_reusable_root() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![2],
            roots: vec![2, 4],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0, 1]),
                n(3, NodeKind::Read, 1, true, vec![]),
                n(4, NodeKind::Add, 1, false, vec![2, 3]),
            ],
        };

        let sites = enumerate_demand_sites(&inst);

        assert!(sites.contains(&DemandSite {
            root: 0,
            consumer: 2,
            input_index: ROOT_OUTPUT_INPUT_INDEX,
            value: 2,
            class: ValueClass::CachedRootOutput,
        }));
    }

    #[test]
    fn root_output_can_be_cached_at_completion_for_later_reuse() {
        // budget 1: under the streaming model the Add folds over reads at peak 0, so
        // budget 1 is feasible — the single resident cell holds the cached root output.
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![2],
            roots: vec![2, 4],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0, 1]),
                n(3, NodeKind::Read, 1, true, vec![]),
                n(4, NodeKind::Add, 1, false, vec![2, 3]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let mut genome = Genome::neutral(&inst, &sites);
        for (idx, site) in sites.iter().enumerate() {
            if site.value == 2 {
                genome.cache_priority[idx] = -1.0;
                genome.cache_priority[idx] = 1.0;
                genome.cache_priority[idx] = 1.0;
            } else {
                genome.cache_priority[idx] = -1.0;
            }
        }

        let score = score_candidate(&inst, &sites, &genome);

        assert_eq!(score.traffic, 3);
        assert_eq!(score.instrs, 2);
        assert_eq!(score.admitted, 2);
    }

    #[test]
    fn prior_demand_uses_materialized_root_output_instead_of_ram_leaf() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![2],
            roots: vec![2, 4],
            nodes: vec![
                OracleNode {
                    id: 0,
                    kind: NodeKind::Read,
                    width: 1,
                    real_dram: true,
                    children: vec![],
                },
                OracleNode {
                    id: 1,
                    kind: NodeKind::Read,
                    width: 1,
                    real_dram: true,
                    children: vec![],
                },
                OracleNode {
                    id: 2,
                    kind: NodeKind::Add,
                    width: 1,
                    real_dram: false,
                    children: vec![0, 1],
                },
                OracleNode {
                    id: 3,
                    kind: NodeKind::Read,
                    width: 1,
                    real_dram: true,
                    children: vec![],
                },
                OracleNode {
                    id: 4,
                    kind: NodeKind::Add,
                    width: 1,
                    real_dram: false,
                    children: vec![2, 3],
                },
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let mut genome = Genome::neutral(&inst, &sites);
        for (idx, site) in sites.iter().enumerate() {
            if site.value == 2 {
                genome.cache_priority[idx] = 1.0;
                genome.cache_priority[idx] = -1.0;
                genome.cache_priority[idx] = 1.0;
            }
        }

        let score = score_candidate(&inst, &sites, &genome);

        assert_eq!(score.traffic, 3);
        assert_eq!(score.instrs, 2);
        assert!(sites
            .iter()
            .any(|site| site.consumer == 4 && site.value == 2));
    }

    #[test]
    fn prior_demand_cannot_reload_root_output_before_producer_runs() {
        let inst = OracleInstance {
            budget: 4,
            reloadable_values: vec![2],
            roots: vec![2, 4],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0, 1]),
                n(3, NodeKind::Read, 1, true, vec![]),
                n(4, NodeKind::Add, 1, false, vec![2, 3]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let mut genome = Genome::neutral(&inst, &sites);
        genome.root_order_key = vec![1.0, 0.0];

        let score = score_candidate(&inst, &sites, &genome);

        assert_eq!(score.traffic, 3);
        assert!(score.feasible);
    }

    #[test]
    fn decodes_root_order_by_continuous_keys_with_stable_ties() {
        let inst = OracleInstance {
            budget: 4,
            reloadable_values: vec![],
            roots: vec![3, 4, 5],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Read, 1, true, vec![]),
                n(3, NodeKind::Add, 1, false, vec![0]),
                n(4, NodeKind::Add, 1, false, vec![1]),
                n(5, NodeKind::Add, 1, false, vec![2]),
            ],
        };
        let genome = Genome {
            root_order_key: vec![0.2, 0.1, 0.2],
            cache_priority: Vec::new(),
        };

        assert_eq!(decode_root_order(&inst, &genome), vec![4, 3, 5]);
    }

    #[test]
    fn unit_members_buckets_occurrences_in_canonical_order() {
        // unit_of (per-occurrence ids from relation_units) → units[u] = ordered members.
        // unit 0 = {0,2}, unit 1 = {1}, unit 2 = {3,4}; members ascending (gate order).
        let unit_of = vec![0u32, 1, 0, 2, 2];
        assert_eq!(
            unit_members(&unit_of),
            vec![vec![0, 2], vec![1], vec![3, 4]]
        );
    }

    #[test]
    fn decode_unit_order_sorts_units_by_key() {
        // The unit-keyed genome holds one key per unit; the unit order is units sorted
        // by key (ties by unit index).
        assert_eq!(decode_unit_order(&[0.5, 0.1, 0.9, 0.1]), vec![1, 3, 0, 2]);
    }

    #[test]
    fn decode_grouped_expands_units_in_canonical_order() {
        // Two units {0,1} and {2,3}; the unit-keyed genome has ONE key per unit. With
        // unit 1 keyed below unit 0 the occurrence order is unit 1's members then unit
        // 0's, each member block intact ⇒ [2,3,0,1].
        let inst = swap_optimizer_fixture(); // roots [2,3,4,5]
        let units = vec![vec![0usize, 1], vec![2, 3]];
        let genome = Genome {
            root_order_key: vec![0.5, 0.1], // one key per unit
            cache_priority: Vec::new(),
        };
        assert_eq!(
            decode_grouped_occurrence_order(&inst, &genome, &units),
            vec![2, 3, 0, 1],
            "units expand whole, ordered by their key"
        );
        // Empty units ⇒ flat per-occurrence decode (genome is then per-occurrence).
        let flat_genome = Genome {
            root_order_key: vec![0.4, 0.1, 0.3, 0.2],
            cache_priority: Vec::new(),
        };
        assert_eq!(
            decode_grouped_occurrence_order(&inst, &flat_genome, &[]),
            decode_root_occurrence_order(&inst, &flat_genome),
        );
    }

    #[test]
    fn grouped_decode_never_splits_a_unit() {
        // Whatever the unit-key values, a unit is indivisible: every occurrence order
        // the grouped decode produces keeps each unit's members in one contiguous run.
        let inst = swap_optimizer_fixture();
        let units = vec![vec![0usize, 2], vec![1, 3]]; // interleaved member indices
        for keys in [[0.1, 0.9], [0.9, 0.1], [0.5, 0.5]] {
            let genome = Genome {
                root_order_key: keys.to_vec(),
                cache_priority: Vec::new(),
            };
            let order = decode_grouped_occurrence_order(&inst, &genome, &units);
            // Each unit occupies one contiguous run.
            for unit in &units {
                let positions: Vec<usize> = unit
                    .iter()
                    .map(|&occ| order.iter().position(|&o| o == occ).unwrap())
                    .collect();
                let (lo, hi) = (
                    *positions.iter().min().unwrap(),
                    *positions.iter().max().unwrap(),
                );
                assert_eq!(hi - lo + 1, unit.len(), "unit {unit:?} split in {order:?}");
            }
        }
    }

    #[test]
    fn unit_swap_neighbor_swaps_whole_units() {
        // With two units, the only adjacent unit-swap turns the base unit order [0,1]
        // into [1,0] ⇒ occurrence order [2,3,0,1] (both members of each unit move).
        let inst = swap_optimizer_fixture();
        let units = vec![vec![0usize, 1], vec![2, 3]];
        let base = unit_neutral_genome(units.len(), &enumerate_demand_sites(&inst));

        let mut out = Vec::new();
        push_unit_swap_neighbors(&base, 16, &mut out);
        let decoded: Vec<Vec<usize>> = out
            .iter()
            .map(|(_, g, _)| decode_grouped_occurrence_order(&inst, g, &units))
            .collect();
        assert!(
            decoded.contains(&vec![2, 3, 0, 1]),
            "unit-swap must move whole units; got {decoded:?}"
        );
    }

    #[test]
    fn grouped_optimizer_with_singleton_units_matches_flat() {
        // When every occurrence is its own singleton unit, the unit-keyed search and the
        // flat search explore the same order space (each unit is one root) and the
        // neutral seed decodes identically, so the grouped optimum equals the flat one.
        // Guards that the unit-keyed re-key degrades cleanly to the historical search.
        let inst = swap_optimizer_fixture();
        let sites = enumerate_demand_sites(&inst);
        let singletons: Vec<Vec<usize>> = (0..inst.roots.len()).map(|i| vec![i]).collect();
        let flat_seeds = vec![Genome::neutral(&inst, &sites)];
        let unit_seeds = vec![unit_neutral_genome(singletons.len(), &sites)];

        let flat = optimize_from_population(&inst, &sites, flat_seeds, 256);
        let grouped =
            optimize_from_population_grouped(&inst, &sites, unit_seeds, 256, &singletons);

        assert_eq!(
            (flat.best_score.traffic, flat.best_score.instrs),
            (grouped.best_score.traffic, grouped.best_score.instrs)
        );
    }

    #[test]
    fn replay_caches_ram_source_when_admit_bias_is_positive() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![1, 2],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Add, 1, false, vec![0]),
                n(2, NodeKind::Add, 1, false, vec![0]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let mut genome = Genome::neutral(&inst, &sites);
        for (idx, site) in sites.iter().enumerate() {
            if site.value == 0 {
                genome.cache_priority[idx] = 1.0;
            }
        }

        let score = score_candidate(&inst, &sites, &genome);

        assert_eq!(score.traffic, 1);
        assert_eq!(score.instrs, 2);
        assert_eq!(score.order, vec![1, 2]);
    }

    #[test]
    fn replay_eagerly_caches_free_capacity_despite_negative_admit_bias() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![1, 2],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Add, 1, false, vec![0]),
                n(2, NodeKind::Add, 1, false, vec![0]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let mut genome = Genome::neutral(&inst, &sites);
        for (idx, site) in sites.iter().enumerate() {
            if site.value == 0 {
                genome.cache_priority[idx] = -1.0;
            }
        }

        let score = score_candidate(&inst, &sites, &genome);

        assert_eq!(score.traffic, 1);
        assert_eq!(score.instrs, 2);
    }

    #[test]
    fn replay_eagerly_caches_future_use_when_capacity_is_free() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![1, 2],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Add, 1, false, vec![0]),
                n(2, NodeKind::Add, 1, false, vec![0]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let genome = Genome::neutral(&inst, &sites);

        let score = score_candidate(&inst, &sites, &genome);

        assert_eq!(score.traffic, 1);
        assert_eq!(score.instrs, 2);
        assert_eq!(score.admitted, 1);
        assert_eq!(score.admit_stats.free_capacity, 1);
        assert_eq!(score.admit_stats.pressure_rejected, 0);
    }

    #[test]
    fn replay_counts_pressure_admission_rejected_by_bias() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![2, 3, 4, 5],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0]),
                n(3, NodeKind::Add, 1, false, vec![1]),
                n(4, NodeKind::Add, 1, false, vec![0]),
                n(5, NodeKind::Add, 1, false, vec![1]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let mut genome = Genome::neutral(&inst, &sites);
        for (idx, site) in sites.iter().enumerate() {
            if site.value == 1 {
                genome.cache_priority[idx] = -1.0;
            }
        }

        let score = score_candidate(&inst, &sites, &genome);

        assert_eq!(score.admit_stats.free_capacity, 1);
        assert_eq!(score.admit_stats.pressure_rejected, 1);
        assert_eq!(score.admit_stats.pressure_admitted, 0);
    }

    #[test]
    fn cache_trace_records_pressure_reject_admit_and_eviction() {
        let inst = trace_guided_cache_fixture();
        let sites = enumerate_demand_sites(&inst);
        let genome = trace_guided_cache_genome(&inst, &sites);

        let (_score, trace) = score_candidate_with_trace(&inst, &sites, &genome);

        assert!(trace
            .events
            .iter()
            .any(|event| matches!(event, CacheTraceEvent::PressureReject { value: 1, .. })));
        assert!(trace
            .events
            .iter()
            .any(|event| matches!(event, CacheTraceEvent::PressureAdmit { value: 2, .. })));
        assert!(trace.events.iter().any(|event| matches!(
            event,
            CacheTraceEvent::Evict {
                victim: 0,
                cause: EvictCause::PressureAdmit { admitted: 2, .. },
                ..
            }
        )));
    }

    #[test]
    fn trace_guided_neighbors_cross_cache_decision_boundaries() {
        let inst = trace_guided_cache_fixture();
        let sites = enumerate_demand_sites(&inst);
        let genome = trace_guided_cache_genome(&inst, &sites);
        let (_score, trace) = score_candidate_with_trace(&inst, &sites, &genome);
        let reject_sites_for_value_1: Vec<_> = sites
            .iter()
            .enumerate()
            .filter_map(|(idx, site)| (site.value == 1).then_some(idx))
            .collect();
        let admit_site_for_value_2 = sites
            .iter()
            .position(|site| site.root == 3 && site.value == 2)
            .expect("value 2 first demand site must exist");
        let victim_keep_site_for_value_0 = sites
            .iter()
            .position(|site| site.root == 2 && site.value == 0)
            .expect("value 0 last keep site before eviction must exist");
        let mut neighbors = Vec::new();

        push_trace_guided_cache_neighbors(&sites, &genome, &trace, 16, &mut neighbors);

        assert!(neighbors.iter().any(|(_, candidate, family)| {
            *family == Some(MoveFamily::AdmitBias)
                && reject_sites_for_value_1
                    .iter()
                    .all(|&idx| candidate.cache_priority[idx] > 0.0)
        }));
        assert!(neighbors.iter().any(|(_, candidate, family)| {
            *family == Some(MoveFamily::KeepBias)
                && candidate.cache_priority[admit_site_for_value_2] > 0.0
        }));
        assert!(neighbors.iter().any(|(_, candidate, family)| {
            *family == Some(MoveFamily::KeepBias)
                && candidate.cache_priority[victim_keep_site_for_value_0] < 0.0
        }));
    }

    #[test]
    fn optimizer_neighbors_include_trace_guided_cache_mutations() {
        let inst = trace_guided_cache_fixture();
        let sites = enumerate_demand_sites(&inst);
        let genome = trace_guided_cache_genome(&inst, &sites);
        let reject_sites_for_value_1: Vec<_> = sites
            .iter()
            .enumerate()
            .filter_map(|(idx, site)| (site.value == 1).then_some(idx))
            .collect();

        let neighbors = neighbor_entries(&inst, &sites, &genome, 64, &[]);

        assert!(neighbors.iter().any(|(_, candidate, family)| {
            *family == Some(MoveFamily::AdmitBias)
                && reject_sites_for_value_1
                    .iter()
                    .all(|&idx| candidate.cache_priority[idx] > 0.0)
        }));
    }

    #[test]
    fn replay_evicts_dead_resident_before_eager_caching() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![2, 3, 4, 5],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0]),
                n(3, NodeKind::Add, 1, false, vec![0]),
                n(4, NodeKind::Add, 1, false, vec![1]),
                n(5, NodeKind::Add, 1, false, vec![1]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let genome = Genome::neutral(&inst, &sites);

        let score = score_candidate(&inst, &sites, &genome);

        assert_eq!(score.traffic, 2);
        assert_eq!(score.instrs, 4);
        assert_eq!(score.evicted, 1);
    }

    #[test]
    fn replay_evicts_lowest_keep_after_use_bias_value() {
        let inst = OracleInstance {
            budget: 2,
            reloadable_values: vec![],
            roots: vec![3, 4, 5, 6, 7, 8],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Read, 1, true, vec![]),
                n(3, NodeKind::Add, 1, false, vec![0]),
                n(4, NodeKind::Add, 1, false, vec![1]),
                n(5, NodeKind::Add, 1, false, vec![2]),
                n(6, NodeKind::Add, 1, false, vec![0]),
                n(7, NodeKind::Add, 1, false, vec![1]),
                n(8, NodeKind::Add, 1, false, vec![2]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let mut genome = Genome::neutral(&inst, &sites);
        for bias in &mut genome.cache_priority {
            *bias = 1.0;
        }
        for (idx, site) in sites.iter().enumerate() {
            genome.cache_priority[idx] = match site.value {
                0 => 1.0,
                1 => -1.0,
                2 => 0.0,
                _ => 0.0,
            };
        }

        let score = score_candidate(&inst, &sites, &genome);

        assert_eq!(score.traffic, 4);
        assert_eq!(score.instrs, 6);
        assert_eq!(score.evicted, 1);
    }

    // NOTE: `transient_compute_storage_evicts_residents_from_same_pool` and
    // `operation_releases_consumed_operand_before_later_child_allocation` were removed
    // with the streaming cost-model correction: they asserted eviction counts driven by
    // the per-node transient pool (`alloc_transient`), which no longer exists — instr
    // results live in the separate accumulator register and operands stream. Eviction
    // under cache pressure is now covered by `cone_fit_evicts_outsider_*` (spill forces
    // eviction) and `fold_over_fused_products_does_not_evict_cross_root_cache` (a fold
    // that streams must NOT evict).

    #[test]
    fn recovery_bias_can_choose_cached_root_reload_over_recompute() {
        let inst = OracleInstance {
            budget: 0,
            reloadable_values: vec![2],
            roots: vec![2, 4],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0, 1]),
                n(3, NodeKind::Read, 1, true, vec![]),
                n(4, NodeKind::Add, 1, false, vec![2, 3]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let mut genome = Genome::neutral(&inst, &sites);
        for (idx, site) in sites.iter().enumerate() {
            if site.value == 2 {
                genome.cache_priority[idx] = -1.0;
                genome.cache_priority[idx] = 1.0;
            }
        }

        let score = score_candidate(&inst, &sites, &genome);

        assert_eq!(score.traffic, 4);
        assert_eq!(score.instrs, 2);
    }

    #[test]
    fn recovery_policy_is_per_site_not_global() {
        // Closes OQ3 (M1): the reload-vs-recompute decision is a PER-SITE policy, so
        // the SAME value can take OPPOSITE policies at two different demand sites —
        // the structural mechanism by which the genome adapts the decision to context
        // (≈ residency), with no residency-aware runtime computation needed.
        //
        // V = node 1 = ext Add{a} (width 4, reloadable root). reload(V)=width 4;
        // recompute(V)=re-read base leaf a (width 1). At budget 0, V is never cached,
        // so each reuse independently reloads (recovery_bias 1.0 → 4*1 >= 4-1) or
        // recomputes (bias 0.0 → cheaper recompute wins). V is reused at R1=Add{V,c}
        // and R2=Add{V,d}. Per-reuse cost: recompute = a(1)+V-Add instr; reload = 4.
        let inst = OracleInstance {
            budget: 0,
            reloadable_values: vec![1],
            roots: vec![1, 3, 5],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),     // a
                n(1, NodeKind::Add, 4, false, vec![0]),    // V (ext root output)
                n(2, NodeKind::Read, 1, true, vec![]),     // c
                n(3, NodeKind::Add, 4, false, vec![1, 2]), // R1 reuses V
                n(4, NodeKind::Read, 1, true, vec![]),     // d
                n(5, NodeKind::Add, 4, false, vec![1, 4]), // R2 reuses V
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let v_at = |consumer: u32| -> usize {
            sites
                .iter()
                .position(|s| s.value == 1 && s.consumer == consumer)
                .unwrap_or_else(|| panic!("no V-demand site at consumer {consumer}"))
        };
        let (r1_site, r2_site) = (v_at(3), v_at(5));

        let mut both_recompute = Genome::neutral(&inst, &sites);
        both_recompute.cache_priority[r1_site] = 0.0;
        both_recompute.cache_priority[r2_site] = 0.0;

        let mut both_reload = Genome::neutral(&inst, &sites);
        both_reload.cache_priority[r1_site] = 1.0;
        both_reload.cache_priority[r2_site] = 1.0;

        let mut mixed = Genome::neutral(&inst, &sites);
        mixed.cache_priority[r1_site] = 1.0; // reload at R1
        mixed.cache_priority[r2_site] = 0.0; // recompute at R2

        let rc = score_candidate(&inst, &sites, &both_recompute);
        let rl = score_candidate(&inst, &sites, &both_reload);
        let mx = score_candidate(&inst, &sites, &mixed);

        // Three DISTINCT outcomes prove each site's policy is applied independently;
        // mixed lands strictly between, with the per-site reload/recompute split.
        assert_eq!((rc.traffic, rc.instrs), (5, 5), "both-recompute");
        assert_eq!((rl.traffic, rl.instrs), (11, 3), "both-reload");
        assert_eq!((mx.traffic, mx.instrs), (8, 4), "mixed (R1 reload, R2 recompute)");
    }

    #[test]
    fn cheap_replay_matches_exact_on_single_root_read_add() {
        let inst = OracleInstance {
            budget: 4,
            reloadable_values: vec![],
            roots: vec![2],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0, 1]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let genome = Genome::neutral(&inst, &sites);

        let cheap = score_candidate(&inst, &sites, &genome);
        let exact = crate::s3_planner::inner_dp::plan_fixed_order(&inst).result;

        assert_eq!((cheap.traffic, cheap.instrs), exact.objective());
    }

    #[test]
    fn cheap_replay_matches_exact_on_cached_shared_source_when_admitted() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![1, 2],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Add, 1, false, vec![0]),
                n(2, NodeKind::Add, 1, false, vec![0]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let mut genome = Genome::neutral(&inst, &sites);
        for bias in &mut genome.cache_priority {
            *bias = 1.0;
        }

        let cheap = score_candidate(&inst, &sites, &genome);
        let exact = crate::s3_planner::inner_dp::plan_fixed_order(&inst).result;

        assert_eq!((cheap.traffic, cheap.instrs), exact.objective());
    }

    #[test]
    fn feasibility_matches_exact_when_cone_peak_exceeds_budget() {
        // Under the single-accumulator streaming model a fold over reads streams
        // (peak 0); infeasibility comes only from SPILL pressure. v = g + h where g,h
        // are each a fold over two ext reads (peak 0): computing the second forces the
        // accumulator to spill its width-4 partial, so peak[v] = 4. At budget 3 the cone
        // cannot be scheduled. The scorer must agree with the exact reference instead of
        // rating it feasible.
        let inst = OracleInstance {
            budget: 3,
            reloadable_values: vec![],
            roots: vec![6],
            nodes: vec![
                n(0, NodeKind::Read, 4, true, vec![]),
                n(1, NodeKind::Read, 4, true, vec![]),
                n(2, NodeKind::Add, 4, false, vec![0, 1]), // g, peak 0
                n(3, NodeKind::Read, 4, true, vec![]),
                n(4, NodeKind::Read, 4, true, vec![]),
                n(5, NodeKind::Add, 4, false, vec![3, 4]), // h, peak 0
                n(6, NodeKind::Add, 4, false, vec![2, 5]), // v, peak = 4 + 0 = 4 > 3
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let genome = Genome::neutral(&inst, &sites);

        let cheap = score_candidate(&inst, &sites, &genome);
        let exact = crate::s3_planner::inner_dp::plan_fixed_order(&inst).result;

        assert!(!exact.feasible, "reference rejects spill peak 4 > budget 3");
        assert_eq!(
            cheap.feasible, exact.feasible,
            "scorer feasibility must match the exact SU spill-peak verdict"
        );
    }

    #[test]
    fn fold_over_fused_products_does_not_evict_cross_root_cache() {
        // B = Add(Mul(r,r), Mul(r,r)) folds two fused products: every operand streams,
        // so peak[B] = 0 and computing B must NOT cost cache. X (read) is cached at A
        // (s0) and reused at C (s2). The corrected cone-fit model keeps X resident
        // through B (no spill), so X is reused at C with no reload — matching the exact
        // reference. The old per-node transient model charged width per Mul and wrongly
        // evicted X (reload at C).
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![1, 8, 9],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),     // X
                n(1, NodeKind::Add, 1, false, vec![0]),    // A (s0), reads X
                n(2, NodeKind::Read, 1, true, vec![]),
                n(3, NodeKind::Read, 1, true, vec![]),
                n(4, NodeKind::Mul, 1, false, vec![2, 3]), // fused product, streams
                n(5, NodeKind::Read, 1, true, vec![]),
                n(6, NodeKind::Read, 1, true, vec![]),
                n(7, NodeKind::Mul, 1, false, vec![5, 6]), // fused product, streams
                n(8, NodeKind::Add, 1, false, vec![4, 7]), // B (s1), peak 0
                n(9, NodeKind::Add, 1, false, vec![0]),    // C (s2), reuses X
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let genome = Genome::neutral(&inst, &sites);

        let cheap = score_candidate(&inst, &sites, &genome);
        let exact = crate::s3_planner::inner_dp::plan_fixed_order(&inst).result;

        assert!(cheap.feasible);
        assert_eq!(cheap.traffic, 5); // X(1) + 4 reads; X stays resident, no reload at C
        assert_eq!((cheap.traffic, cheap.instrs), exact.objective());
    }

    #[test]
    fn cone_fit_evicts_outsider_when_spill_plus_resident_exceeds_budget() {
        // Fold-of-folds B (s1) spills (peak 1). X cached at A (s0), reused at C (s2).
        // At budget 1, X outsider(1) + peak[B](1) = 2 > 1, so the scorer must evict X
        // before B and re-read it at C — matching the exact reference (4,5).
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![3, 6, 7],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Read, 1, true, vec![]),
                n(3, NodeKind::Add, 1, false, vec![0]),
                n(4, NodeKind::Add, 1, false, vec![1]),
                n(5, NodeKind::Add, 1, false, vec![2]),
                n(6, NodeKind::Add, 1, false, vec![4, 5]),
                n(7, NodeKind::Add, 1, false, vec![0]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let genome = Genome::neutral(&inst, &sites);

        let cheap = score_candidate(&inst, &sites, &genome);
        let exact = crate::s3_planner::inner_dp::plan_fixed_order(&inst).result;

        assert!(cheap.feasible);
        assert_eq!((cheap.traffic, cheap.instrs), exact.objective()); // (4, 5)
    }

    #[test]
    fn small_non_crossing_perturbation_preserves_score() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![1, 2],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Add, 1, false, vec![0]),
                n(2, NodeKind::Add, 1, false, vec![0]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let genome = Genome::neutral(&inst, &sites);
        let perturbed = perturb_one_gene(&genome, 0, 0.01);

        let a = score_candidate(&inst, &sites, &genome);
        let b = score_candidate(&inst, &sites, &perturbed);

        assert_eq!(
            (a.order, a.traffic, a.instrs),
            (b.order, b.traffic, b.instrs)
        );
    }

    #[test]
    fn random_seed_and_mutation_stay_in_normalized_ranges() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![1, 2],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Add, 1, false, vec![0]),
                n(2, NodeKind::Add, 1, false, vec![0]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let genome = deterministic_smoke_genome(&inst, &sites, 7);

        assert_normalized_genome(&genome);

        let root_idx = 0;
        let admit_idx = genome.root_order_key.len();
        let recovery_idx = admit_idx + genome.cache_priority.len();
        let keep_idx = recovery_idx + genome.cache_priority.len();

        assert_normalized_genome(&perturb_one_gene(&genome, root_idx, 100.0));
        assert_normalized_genome(&perturb_one_gene(&genome, admit_idx, 100.0));
        assert_normalized_genome(&perturb_one_gene(&genome, recovery_idx, -100.0));
        assert_normalized_genome(&perturb_one_gene(&genome, keep_idx, 100.0));
    }

    #[test]
    fn smoke_population_starts_with_neutral_and_reversed_order() {
        let inst = OracleInstance {
            budget: 2,
            reloadable_values: vec![],
            roots: vec![2, 3, 4],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0]),
                n(3, NodeKind::Add, 1, false, vec![1]),
                n(4, NodeKind::Add, 1, false, vec![0, 1]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);

        let genomes = smoke_genome_population(&inst, &sites, 4);

        assert_eq!(genomes.len(), 4);
        assert_eq!(decode_root_order(&inst, &genomes[0]), vec![2, 3, 4]);
        assert_eq!(genomes[0], Genome::neutral(&inst, &sites));
        assert_eq!(decode_root_order(&inst, &genomes[1]), vec![4, 3, 2]);
    }

    #[test]
    fn reuse_weighted_smoke_genome_prefers_dense_future_reuse() {
        let inst = OracleInstance {
            budget: 2,
            reloadable_values: vec![],
            roots: vec![2, 3, 4, 6],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 2, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0]),
                n(3, NodeKind::Add, 1, false, vec![0]),
                n(4, NodeKind::Add, 1, false, vec![1]),
                n(5, NodeKind::Read, 1, true, vec![]),
                n(6, NodeKind::Add, 1, false, vec![2, 5]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);

        let genome = reuse_weighted_smoke_genome(&inst, &sites);

        assert!(genome.cache_priority.iter().all(|&bias| bias > 0.0));
        assert!(genome.cache_priority.iter().all(|&bias| bias >= 0.0));
        assert!(genome.cache_priority[0] > genome.cache_priority[1]);
        assert_eq!(decode_root_order(&inst, &genome), inst.roots);
    }

    #[test]
    fn local_optimizer_improves_by_swapping_adjacent_roots() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![2, 3, 4, 5],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0]),
                n(3, NodeKind::Add, 1, false, vec![1]),
                n(4, NodeKind::Add, 1, false, vec![0]),
                n(5, NodeKind::Add, 1, false, vec![1]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let neutral = Genome::neutral(&inst, &sites);
        let baseline = score_candidate(&inst, &sites, &neutral);

        let optimized = optimize_from_population(&inst, &sites, vec![neutral], 16);

        assert!(objective_less(&optimized.best_score, &baseline));
        assert_eq!(
            (optimized.best_score.traffic, optimized.best_score.instrs),
            (2, 4)
        );
        assert_eq!(optimized.best_score.order, vec![2, 4, 3, 5]);
        assert_eq!(optimized.accepted.root_swaps, 1);
        assert_eq!(optimized.accepted.total(), 1);
        assert_eq!(optimized.family_stats.root_swaps.selected, 1);
        assert!(optimized.family_stats.root_swaps.improving >= 1);
        assert!(optimized.evals > 1);
    }

    #[test]
    fn compact_smoke_final_best_retains_optimizer_incumbent() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![2, 3, 4, 5],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0]),
                n(3, NodeKind::Add, 1, false, vec![1]),
                n(4, NodeKind::Add, 1, false, vec![0]),
                n(5, NodeKind::Add, 1, false, vec![1]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);

        let smoke = compact_smoke(&inst, &sites, 4, 16, 1, 1);

        assert_eq!(
            (
                smoke.optimized.best_score.traffic,
                smoke.optimized.best_score.instrs
            ),
            (2, 4)
        );
        assert_eq!(
            (
                smoke.final_states.best.traffic,
                smoke.final_states.best.instrs
            ),
            (2, 4)
        );
    }

    #[test]
    fn local_optimizer_improves_by_inserting_root() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![3, 4, 5, 6, 7, 8],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Read, 1, true, vec![]),
                n(3, NodeKind::Add, 1, false, vec![0]),
                n(4, NodeKind::Add, 1, false, vec![1]),
                n(5, NodeKind::Add, 1, false, vec![2]),
                n(6, NodeKind::Add, 1, false, vec![1]),
                n(7, NodeKind::Add, 1, false, vec![2]),
                n(8, NodeKind::Add, 1, false, vec![0]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let neutral = Genome::neutral(&inst, &sites);
        let baseline = score_candidate(&inst, &sites, &neutral);

        let optimized = optimize_from_population(&inst, &sites, vec![neutral], 128);

        assert!(objective_less(&optimized.best_score, &baseline));
        assert_eq!(
            (optimized.best_score.traffic, optimized.best_score.instrs),
            (4, 6)
        );
        assert!(optimized.accepted.root_inserts >= 1);
        assert_eq!(
            optimized.family_stats.root_inserts.selected,
            optimized.accepted.root_inserts
        );
    }

    #[test]
    fn unit_draw_is_in_unit_interval_and_deterministic() {
        for seed in [0u64, 1, 42, 1 << 40, u64::MAX] {
            let d = unit_draw(seed);
            assert!((0.0..1.0).contains(&d), "draw {d} must lie in [0, 1)");
            assert_eq!(d, unit_draw(seed), "same seed must reproduce the same draw");
        }
        assert_ne!(
            unit_draw(1),
            unit_draw(2),
            "distinct seeds should produce distinct draws"
        );
    }

    #[test]
    fn sa_temperature_starts_hot_and_cools_to_zero() {
        assert_eq!(sa_temperature(0, 1000), SA_INITIAL_TEMPERATURE);
        assert_eq!(sa_temperature(1000, 1000), 0.0);
        assert_eq!(
            sa_temperature(5000, 1000),
            0.0,
            "temperature is clamped to 0 at/after full budget"
        );
        assert_eq!(
            sa_temperature(10, 0),
            0.0,
            "zero budget degenerates to zero temperature"
        );
        let mid = sa_temperature(500, 1000);
        assert!(mid > 0.0 && mid < SA_INITIAL_TEMPERATURE);
        assert!(
            sa_temperature(250, 1000) > sa_temperature(750, 1000),
            "temperature must decrease monotonically as budget is spent"
        );
    }

    #[test]
    fn best_uphill_neighbor_picks_gentlest_feasible_worse_traffic() {
        let current = candidate_score(10, 20);
        let scored = vec![
            scored_test_candidate(0, candidate_score(9, 20), MoveFamily::RootSwap), // improving
            scored_test_candidate(1, candidate_score(13, 20), MoveFamily::RootInsert), // +3
            scored_test_candidate(2, candidate_score(11, 20), MoveFamily::RootReverse), // +1, gentlest
            scored_test_candidate(3, candidate_score(12, 20), MoveFamily::RootSwap), // +2
        ];
        assert_eq!(best_uphill_neighbor(&scored, &current), Some(2));
    }

    #[test]
    fn best_uphill_neighbor_ignores_improving_equal_and_infeasible() {
        let current = candidate_score(10, 20);
        let mut infeasible_worse = candidate_score(11, 20);
        infeasible_worse.feasible = false;
        let scored = vec![
            scored_test_candidate(0, candidate_score(9, 20), MoveFamily::RootSwap), // improving
            scored_test_candidate(1, candidate_score(10, 20), MoveFamily::RootSwap), // equal traffic
            scored_test_candidate(2, candidate_score(10, 25), MoveFamily::RootSwap), // equal traffic, worse instr only
            scored_test_candidate(3, infeasible_worse, MoveFamily::RootInsert),      // worse but infeasible
        ];
        assert_eq!(best_uphill_neighbor(&scored, &current), None);
    }

    #[test]
    fn metropolis_rejects_worse_candidate_at_zero_temperature() {
        // T <= 0 degenerates to hill-climbing: a strictly-worse candidate is never accepted,
        // regardless of the draw.
        assert!(!metropolis_accepts(5.0, 0.0, 0.0));
        assert!(!metropolis_accepts(0.001, 0.0, 0.0));
    }

    #[test]
    fn metropolis_accepts_worse_candidate_when_draw_below_boltzmann_probability() {
        // delta=1, T=1 => p = e^-1 ~= 0.3679; a draw below p accepts the uphill move.
        assert!(metropolis_accepts(1.0, 1.0, 0.30));
    }

    #[test]
    fn metropolis_rejects_worse_candidate_when_draw_above_boltzmann_probability() {
        // Same p ~= 0.3679; a draw above p rejects.
        assert!(!metropolis_accepts(1.0, 1.0, 0.50));
    }

    #[test]
    fn metropolis_acceptance_probability_shrinks_as_temperature_cools() {
        // Fixed uphill delta and draw: a hot temperature accepts, a cold one rejects.
        let delta = 1.0;
        let draw = 0.30;
        assert!(
            metropolis_accepts(delta, 1.0, draw),
            "hot temperature (p~=0.368) should accept draw 0.30"
        );
        assert!(
            !metropolis_accepts(delta, 0.30, draw),
            "cold temperature (p~=0.036) should reject draw 0.30"
        );
    }

    #[test]
    fn segment_reverse_neighbors_reverse_contiguous_runs_of_length_three_or_more() {
        // 5 roots; neutral genome decodes to the identity occurrence order [0,1,2,3,4].
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![5, 6, 7, 8, 9],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Read, 1, true, vec![]),
                n(3, NodeKind::Read, 1, true, vec![]),
                n(4, NodeKind::Read, 1, true, vec![]),
                n(5, NodeKind::Add, 1, false, vec![0]),
                n(6, NodeKind::Add, 1, false, vec![1]),
                n(7, NodeKind::Add, 1, false, vec![2]),
                n(8, NodeKind::Add, 1, false, vec![3]),
                n(9, NodeKind::Add, 1, false, vec![4]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let base = Genome::neutral(&inst, &sites);
        assert_eq!(
            decode_root_occurrence_order(&inst, &base),
            vec![0, 1, 2, 3, 4],
            "neutral genome must decode to the identity occurrence order"
        );

        let mut out = Vec::new();
        push_root_reverse_neighbors(&inst, &base, usize::MAX, &mut out);

        let orders: Vec<Vec<usize>> = out
            .iter()
            .map(|(_, genome, _)| decode_root_occurrence_order(&inst, genome))
            .collect();

        // Every neighbor is a valid permutation of the five occurrences.
        for order in &orders {
            let mut sorted = order.clone();
            sorted.sort_unstable();
            assert_eq!(sorted, vec![0, 1, 2, 3, 4], "neighbor must be a permutation");
        }

        // Canonical length-3+ reversals are present.
        assert!(orders.contains(&vec![2, 1, 0, 3, 4]), "must include reverse [0..=2]");
        assert!(orders.contains(&vec![0, 3, 2, 1, 4]), "must include reverse [1..=3]");
        assert!(orders.contains(&vec![4, 3, 2, 1, 0]), "must include reverse [0..=4]");

        // Every emitted move is tagged RootReverse.
        assert!(
            out.iter()
                .all(|(_, _, family)| *family == Some(MoveFamily::RootReverse)),
            "all neighbors must be RootReverse moves"
        );

        // Length-2 reversals duplicate RootSwap's adjacent swaps and must be skipped,
        // and the no-op identity order must never be emitted.
        assert!(
            !orders.contains(&vec![1, 0, 2, 3, 4]),
            "length-2 reversal duplicates RootSwap; must be skipped"
        );
        assert!(
            !orders.contains(&vec![0, 1, 2, 3, 4]),
            "must not emit the identity order"
        );
    }

    #[test]
    fn neighbor_entries_include_root_reverse_moves() {
        let inst = OracleInstance {
            budget: 4,
            reloadable_values: vec![],
            roots: vec![5, 6, 7, 8, 9],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Read, 1, true, vec![]),
                n(3, NodeKind::Read, 1, true, vec![]),
                n(4, NodeKind::Read, 1, true, vec![]),
                n(5, NodeKind::Add, 1, false, vec![0]),
                n(6, NodeKind::Add, 1, false, vec![1]),
                n(7, NodeKind::Add, 1, false, vec![2]),
                n(8, NodeKind::Add, 1, false, vec![3]),
                n(9, NodeKind::Add, 1, false, vec![4]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let base = Genome::neutral(&inst, &sites);
        let neighbors = neighbor_entries(&inst, &sites, &base, 64, &[]);
        assert!(
            neighbors
                .iter()
                .any(|(_, _, family)| *family == Some(MoveFamily::RootReverse)),
            "neighbor batch must include RootReverse 2-opt moves"
        );
    }

    #[test]
    fn neighbor_batch_reserves_slots_for_cache_bias_families() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![6, 7, 8, 9, 10, 11, 12, 13],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Read, 1, true, vec![]),
                n(3, NodeKind::Read, 1, true, vec![]),
                n(4, NodeKind::Read, 1, true, vec![]),
                n(5, NodeKind::Read, 1, true, vec![]),
                n(6, NodeKind::Add, 1, false, vec![0]),
                n(7, NodeKind::Add, 1, false, vec![1]),
                n(8, NodeKind::Add, 1, false, vec![2]),
                n(9, NodeKind::Add, 1, false, vec![3]),
                n(10, NodeKind::Add, 1, false, vec![4]),
                n(11, NodeKind::Add, 1, false, vec![5]),
                n(12, NodeKind::Add, 1, false, vec![0]),
                n(13, NodeKind::Add, 1, false, vec![1]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let neutral = Genome::neutral(&inst, &sites);

        let neighbors = neighbor_entries(&inst, &sites, &neutral, 12, &[]);

        assert_eq!(neighbors.len(), 12);
        assert!(neighbors
            .iter()
            .any(|(_, _, family)| *family == Some(MoveFamily::RootInsert)));
        assert!(neighbors
            .iter()
            .any(|(_, _, family)| *family == Some(MoveFamily::AdmitBias)));
        assert!(neighbors
            .iter()
            .any(|(_, _, family)| *family == Some(MoveFamily::KeepBias)));
    }

    #[test]
    fn objective_stats_reports_min_percentiles_and_max() {
        let mut objectives = vec![(5, 50), (1, 10), (3, 30), (2, 20), (4, 40)];

        let stats = objective_stats(&mut objectives);

        assert_eq!(stats.min, Some((1, 10)));
        assert_eq!(stats.p05, Some((1, 10)));
        assert_eq!(stats.p25, Some((2, 20)));
        assert_eq!(stats.p50, Some((3, 30)));
        assert_eq!(stats.p75, Some((4, 40)));
        assert_eq!(stats.p95, Some((5, 50)));
        assert_eq!(stats.max, Some((5, 50)));
    }

    #[test]
    fn family_stats_track_best_candidate_objective() {
        let mut stats = MoveFamilyStats::default();
        let worse = candidate_score(10, 20);
        let better = candidate_score(8, 25);
        let best = candidate_score(8, 18);

        stats.record_candidate(MoveFamily::KeepBias, &worse, false);
        stats.record_candidate(MoveFamily::KeepBias, &better, true);
        stats.record_candidate(MoveFamily::KeepBias, &best, true);

        assert_eq!(stats.keep_after_use_bias.tried, 3);
        assert_eq!(stats.keep_after_use_bias.improving, 2);
        assert_eq!(stats.keep_after_use_bias.best, Some((8, 18)));
        assert_eq!(stats.keep_after_use_bias.best_improving, Some((8, 18)));
    }

    #[test]
    fn plateau_selection_accepts_equal_cache_neighbor_when_budget_remains() {
        let current = candidate_score(10, 20);
        let root_equal = scored_test_candidate(0, candidate_score(10, 20), MoveFamily::RootSwap);
        let cache_equal = scored_test_candidate(1, candidate_score(10, 20), MoveFamily::KeepBias);
        let worse_cache = scored_test_candidate(2, candidate_score(11, 20), MoveFamily::AdmitBias);
        let scored = vec![root_equal, cache_equal.clone(), worse_cache];

        let selected = select_optimizer_neighbor(&scored, &current, 1);

        assert_eq!(selected, OptimizerStep::Sideways(1));
    }

    #[test]
    fn plateau_selection_prefers_strict_improvement_over_sideways_cache_neighbor() {
        let current = candidate_score(10, 20);
        let cache_equal = scored_test_candidate(0, candidate_score(10, 20), MoveFamily::KeepBias);
        let improving_root =
            scored_test_candidate(1, candidate_score(9, 25), MoveFamily::RootInsert);
        let scored = vec![cache_equal, improving_root];

        let selected = select_optimizer_neighbor(&scored, &current, 1);

        assert_eq!(selected, OptimizerStep::Improving(1));
    }

    #[test]
    fn optimizer_beam_keeps_multiple_scored_seed_states() {
        let scored = vec![
            scored_test_candidate(0, candidate_score(12, 20), MoveFamily::RootSwap),
            scored_test_candidate(1, candidate_score(10, 22), MoveFamily::RootInsert),
            scored_test_candidate(2, candidate_score(11, 18), MoveFamily::KeepBias),
        ];

        let states = optimizer_beam_from_seed_scores(scored, 2);

        assert_eq!(states.len(), 2);
        assert_eq!((states[0].score.traffic, states[0].score.instrs), (10, 22));
        assert_eq!((states[1].score.traffic, states[1].score.instrs), (11, 18));
        assert!(states
            .iter()
            .all(|state| state.plateau_remaining == CACHE_PLATEAU_STEPS));
    }

    #[test]
    fn optimizer_beam_dedups_states_with_equal_order_and_objective() {
        // Two distinct genomes that decode to the SAME root order and the SAME
        // objective are redundant beam starts: greedy descent from either explores
        // the identical neighborhood. Dedup must collapse them by (order, objective),
        // NOT by byte-equal genome — random-key seeds almost never collide bytewise,
        // so full-genome dedup would admit redundant states on small root sets.
        let same_order = vec![5u32, 6, 7];
        let mut a = candidate_score(10, 22);
        a.order = same_order.clone();
        let mut b = candidate_score(10, 22);
        b.order = same_order.clone();
        let scored = vec![
            scored_test_candidate(0, a, MoveFamily::RootSwap),
            scored_test_candidate(1, b, MoveFamily::RootInsert),
        ];

        let states = optimizer_beam_from_seed_scores(scored, 8);

        assert_eq!(states.len(), 1);
        assert_eq!(states[0].score.order, same_order);
    }

    #[test]
    fn beam_width_scales_with_budget_to_avoid_dilution() {
        // Beam width must track the eval budget: a single greedy descent needs
        // ~BEAM_STATE_MIN_BUDGET evals to converge, so opening more states than the
        // budget can fund starves the best trajectory and regresses (measured: width 8
        // @ budget 2000 = 402→378). Width 1 below the floor; widen only with surplus.
        assert_eq!(beam_width_for_budget(16), 1);
        assert_eq!(beam_width_for_budget(BEAM_STATE_MIN_BUDGET - 1), 1);
        assert_eq!(beam_width_for_budget(2_000), 2);
        assert_eq!(beam_width_for_budget(16_000), OPTIMIZER_BEAM_WIDTH);
        assert!(beam_width_for_budget(usize::MAX) <= OPTIMIZER_BEAM_WIDTH);
        assert!(beam_width_for_budget(1) >= 1);
    }

    #[test]
    fn advance_optimizer_state_updates_global_best_on_improvement() {
        let inst = swap_optimizer_fixture();
        let sites = enumerate_demand_sites(&inst);
        let genome = Genome::neutral(&inst, &sites);
        let score = score_candidate(&inst, &sites, &genome);
        let mut state = OptimizerState {
            genome: genome.clone(),
            score: score.clone(),
            plateau_remaining: CACHE_PLATEAU_STEPS,
        };
        let mut best_genome = genome;
        let mut best_score = score;
        let mut evals = 1usize;
        let mut accepted = AcceptedMoves::default();
        let mut family_stats = MoveFamilyStats::default();

        let moved = advance_optimizer_state(
            &inst,
            &sites,
            &mut state,
            16,
            &mut evals,
            &mut best_genome,
            &mut best_score,
            &mut accepted,
            &mut family_stats,
            &[],
        );

        assert!(moved);
        assert_eq!((best_score.traffic, best_score.instrs), (2, 4));
        assert_eq!(accepted.root_swaps, 1);
        assert_eq!(family_stats.root_swaps.selected, 1);
    }

    #[test]
    fn advance_drives_sa_stop_branch_and_preserves_global_best() {
        // Drives the SA uphill (Stop) branch of advance_optimizer_state end-to-end and
        // asserts the safety property both reviews leaned on: the GLOBAL best is never
        // worsened by an uphill move. A 4-root no-cache fixture converges in a couple of
        // advances, after which advance hits the Stop arm — either SA accepts an uphill move
        // (state becomes worse than best) or rejects and drops the state (moved=false). Both
        // transit the branch.
        let inst = swap_optimizer_fixture();
        let sites = enumerate_demand_sites(&inst);
        let genome = Genome::neutral(&inst, &sites);
        let score = score_candidate(&inst, &sites, &genome);
        let mut state = OptimizerState {
            genome: genome.clone(),
            score: score.clone(),
            plateau_remaining: CACHE_PLATEAU_STEPS,
        };
        let mut best_genome = genome;
        let mut best_score = score.clone();
        let mut evals = 1usize;
        let mut accepted = AcceptedMoves::default();
        let mut family_stats = MoveFamilyStats::default();
        // Large eval budget so the 4-root state fully converges and reaches the Stop arm
        // well before the budget is spent (a small budget just times out mid-search).
        const BUDGET: usize = 2_000;

        let mut prev_best = best_score.traffic;
        let mut sa_uphill_observed = false;
        let mut stop_reached = false;
        for _ in 0..200 {
            if evals >= BUDGET {
                break;
            }
            let moved = advance_optimizer_state(
                &inst,
                &sites,
                &mut state,
                BUDGET,
                &mut evals,
                &mut best_genome,
                &mut best_score,
                &mut accepted,
                &mut family_stats,
                &[],
            );
            // Global best must be monotonically non-worsening — SA never writes a worse value.
            assert!(
                best_score.traffic <= prev_best,
                "global best regressed {prev_best} -> {}",
                best_score.traffic
            );
            prev_best = best_score.traffic;
            if !moved {
                stop_reached = true;
                break;
            }
            // An uphill state strictly worse than the preserved best ⇒ the SA Stop branch
            // accepted a worsening move.
            if state.score.traffic > best_score.traffic {
                sa_uphill_observed = true;
            }
        }
        assert!(
            sa_uphill_observed || stop_reached,
            "SA Stop branch was never exercised (state never stalled)"
        );
        assert!(best_score.feasible, "global best must stay feasible");
        assert!(
            best_score.traffic <= score.traffic,
            "global best must not exceed the neutral start"
        );
    }

    #[test]
    fn population_summary_retains_best_order() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![2, 3, 4, 5],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0]),
                n(3, NodeKind::Add, 1, false, vec![1]),
                n(4, NodeKind::Add, 1, false, vec![0]),
                n(5, NodeKind::Add, 1, false, vec![1]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let neutral = Genome::neutral(&inst, &sites);
        let mut swapped = Genome::neutral(&inst, &sites);
        swapped.root_order_key.swap(1, 2);

        let summary = score_population(&inst, &sites, vec![neutral, swapped]);

        assert_eq!((summary.best.traffic, summary.best.instrs), (2, 4));
        assert_eq!(summary.best.order, vec![2, 4, 3, 5]);
        assert_eq!(summary.objectives.min, Some((2, 4)));
        assert_eq!(summary.objectives.max, Some((3, 4)));
        assert_eq!(summary.total, 2);
        assert_eq!(summary.infeasible, 0);
    }

    #[test]
    fn parallel_population_summary_matches_sequential() {
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![2, 3, 4, 5],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![0]),
                n(3, NodeKind::Add, 1, false, vec![1]),
                n(4, NodeKind::Add, 1, false, vec![0]),
                n(5, NodeKind::Add, 1, false, vec![1]),
            ],
        };
        let sites = enumerate_demand_sites(&inst);
        let genomes = smoke_genome_population(&inst, &sites, 16);

        let sequential = score_population(&inst, &sites, genomes.clone());
        let parallel = score_population_parallel(&inst, &sites, genomes, 3);

        assert_eq!(parallel.best, sequential.best);
        assert_eq!(parallel.median, sequential.median);
        assert_eq!(parallel.objectives, sequential.objectives);
        assert_eq!(parallel.feasible, sequential.feasible);
        assert_eq!(parallel.infeasible, sequential.infeasible);
        assert_eq!(parallel.total, sequential.total);
    }

    fn deterministic_smoke_genome(
        inst: &OracleInstance,
        sites: &[DemandSite],
        seed: u64,
    ) -> Genome {
        let mut rng = SmokeRng::new(seed);
        let mut genome = Genome::neutral(inst, sites);
        for key in &mut genome.root_order_key {
            *key = rng.next_unit();
        }
        for bias in &mut genome.cache_priority {
            *bias = rng.next_signed();
        }
        for bias in &mut genome.cache_priority {
            *bias = rng.next_signed();
        }
        for bias in &mut genome.cache_priority {
            *bias = rng.next_signed();
        }
        genome
    }

    fn reuse_weighted_smoke_genome(inst: &OracleInstance, sites: &[DemandSite]) -> Genome {
        let mut genome = Genome::neutral(inst, sites);
        for bias in &mut genome.cache_priority {
            *bias = 1.0;
        }
        for (idx, site) in sites.iter().enumerate() {
            if site.class == ValueClass::CachedRootOutput {
                let reload = inst.nodes[site.value as usize].width as f64;
                let recompute = estimate_recompute_traffic(inst, site.value) as f64;
                genome.cache_priority[idx] = if recompute > reload { 1.0 } else { 0.0 };
            }
        }

        let mut demand_count = vec![0u32; inst.nodes.len()];
        for site in sites {
            demand_count[site.value as usize] += 1;
        }
        let mut density = vec![0.0; inst.nodes.len()];
        let mut max_density = 0.0f64;
        for (idx, slot) in density.iter_mut().enumerate() {
            let width = inst.nodes[idx].width.max(1) as f64;
            *slot = demand_count[idx] as f64 / width;
            max_density = max_density.max(*slot);
        }
        if max_density > 0.0 {
            for (idx, site) in sites.iter().enumerate() {
                genome.cache_priority[idx] = density[site.value as usize] / max_density;
            }
        }
        genome
    }

    fn estimate_recompute_traffic(inst: &OracleInstance, value: u32) -> u64 {
        let mut seen = vec![false; inst.nodes.len()];
        let mut stack = vec![value];
        let mut traffic = 0u64;
        while let Some(id) = stack.pop() {
            if seen[id as usize] {
                continue;
            }
            seen[id as usize] = true;
            let node = &inst.nodes[id as usize];
            if node.real_dram {
                traffic += node.width as u64;
            }
            for &child in &node.children {
                stack.push(child);
            }
        }
        traffic
    }

    #[derive(Clone, Debug)]
    pub(crate) struct OptimizerResult {
        pub(crate) best_genome: Genome,
        pub(crate) best_score: CandidateScore,
        evals: usize,
        iterations: usize,
        beam_states: usize,
        accepted: AcceptedMoves,
        family_stats: MoveFamilyStats,
    }

    #[derive(Clone, Debug)]
    struct OptimizerState {
        genome: Genome,
        score: CandidateScore,
        plateau_remaining: usize,
    }

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct AcceptedMoves {
        root_swaps: usize,
        root_inserts: usize,
        root_reverses: usize,
        admit_bias: usize,
        recovery_bias: usize,
        keep_after_use_bias: usize,
    }

    impl AcceptedMoves {
        fn total(&self) -> usize {
            self.root_swaps
                + self.root_inserts
                + self.root_reverses
                + self.admit_bias
                + self.recovery_bias
                + self.keep_after_use_bias
        }

        fn add(&mut self, family: MoveFamily) {
            match family {
                MoveFamily::RootSwap => self.root_swaps += 1,
                MoveFamily::RootInsert => self.root_inserts += 1,
                MoveFamily::RootReverse => self.root_reverses += 1,
                MoveFamily::AdmitBias => self.admit_bias += 1,
                MoveFamily::RecoveryBias => self.recovery_bias += 1,
                MoveFamily::KeepBias => self.keep_after_use_bias += 1,
            }
        }
    }

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct MoveFamilyCounters {
        tried: usize,
        improving: usize,
        selected: usize,
        best: Option<(u64, u64)>,
        best_improving: Option<(u64, u64)>,
    }

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct MoveFamilyStats {
        root_swaps: MoveFamilyCounters,
        root_inserts: MoveFamilyCounters,
        root_reverses: MoveFamilyCounters,
        admit_bias: MoveFamilyCounters,
        recovery_bias: MoveFamilyCounters,
        keep_after_use_bias: MoveFamilyCounters,
    }

    impl MoveFamilyStats {
        fn counters_mut(&mut self, family: MoveFamily) -> &mut MoveFamilyCounters {
            match family {
                MoveFamily::RootSwap => &mut self.root_swaps,
                MoveFamily::RootInsert => &mut self.root_inserts,
                MoveFamily::RootReverse => &mut self.root_reverses,
                MoveFamily::AdmitBias => &mut self.admit_bias,
                MoveFamily::RecoveryBias => &mut self.recovery_bias,
                MoveFamily::KeepBias => &mut self.keep_after_use_bias,
            }
        }

        fn record_candidate(&mut self, family: MoveFamily, score: &CandidateScore, improved: bool) {
            let counters = self.counters_mut(family);
            counters.tried += 1;
            if improved {
                counters.improving += 1;
                if score.feasible {
                    let objective = (score.traffic, score.instrs);
                    if counters.best_improving.is_none_or(|best| objective < best) {
                        counters.best_improving = Some(objective);
                    }
                }
            }
            if score.feasible {
                let objective = (score.traffic, score.instrs);
                if counters.best.is_none_or(|best| objective < best) {
                    counters.best = Some(objective);
                }
            }
        }

        fn record_selected(&mut self, family: MoveFamily) {
            self.counters_mut(family).selected += 1;
        }

        fn merge(&mut self, other: MoveFamilyStats) {
            merge_counters(&mut self.root_swaps, other.root_swaps);
            merge_counters(&mut self.root_inserts, other.root_inserts);
            merge_counters(&mut self.root_reverses, other.root_reverses);
            merge_counters(&mut self.admit_bias, other.admit_bias);
            merge_counters(&mut self.recovery_bias, other.recovery_bias);
            merge_counters(&mut self.keep_after_use_bias, other.keep_after_use_bias);
        }
    }

    fn merge_counters(dst: &mut MoveFamilyCounters, src: MoveFamilyCounters) {
        dst.tried += src.tried;
        dst.improving += src.improving;
        dst.selected += src.selected;
        if let Some(objective) = src.best {
            if dst.best.is_none_or(|best| objective < best) {
                dst.best = Some(objective);
            }
        }
        if let Some(objective) = src.best_improving {
            if dst.best_improving.is_none_or(|best| objective < best) {
                dst.best_improving = Some(objective);
            }
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum MoveFamily {
        RootSwap,
        RootInsert,
        RootReverse,
        AdmitBias,
        RecoveryBias,
        KeepBias,
    }

    #[derive(Clone, Debug)]
    struct ScoredGenome {
        index: usize,
        genome: Genome,
        score: CandidateScore,
        family: Option<MoveFamily>,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum OptimizerStep {
        Improving(usize),
        Sideways(usize),
        Stop,
    }

    #[derive(Clone, Debug)]
    struct PopulationSummary {
        best: CandidateScore,
        median: Option<(u64, u64)>,
        objectives: ObjectiveStats,
        feasible: usize,
        infeasible: usize,
        total: usize,
    }

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct ObjectiveStats {
        min: Option<(u64, u64)>,
        p05: Option<(u64, u64)>,
        p25: Option<(u64, u64)>,
        p50: Option<(u64, u64)>,
        p75: Option<(u64, u64)>,
        p95: Option<(u64, u64)>,
        max: Option<(u64, u64)>,
    }

    fn score_population(
        inst: &OracleInstance,
        sites: &[DemandSite],
        genomes: Vec<Genome>,
    ) -> PopulationSummary {
        assert!(!genomes.is_empty(), "population must not be empty");

        let mut iter = genomes.into_iter();
        let first_genome = iter.next().expect("population must not be empty");
        let mut best = score_candidate(inst, sites, &first_genome);
        let mut feasible_objectives = Vec::new();
        let mut infeasible = 0usize;
        let mut total = 1usize;
        if best.feasible {
            feasible_objectives.push((best.traffic, best.instrs));
        } else {
            infeasible += 1;
        }

        for genome in iter {
            let score = score_candidate(inst, sites, &genome);
            total += 1;
            if score.feasible {
                feasible_objectives.push((score.traffic, score.instrs));
            } else {
                infeasible += 1;
            }
            if objective_less(&score, &best) {
                best = score;
            }
        }

        let objectives = objective_stats(&mut feasible_objectives);
        let median = objectives.p50;

        PopulationSummary {
            best,
            median,
            objectives,
            feasible: feasible_objectives.len(),
            infeasible,
            total,
        }
    }

    fn score_population_parallel(
        inst: &OracleInstance,
        sites: &[DemandSite],
        genomes: Vec<Genome>,
        workers: usize,
    ) -> PopulationSummary {
        let scored = score_genomes_parallel(
            inst,
            sites,
            genomes
                .into_iter()
                .enumerate()
                .map(|(index, genome)| (index, genome, None))
                .collect(),
            workers,
            &[],
        );
        summarize_scored_population(scored)
    }

    fn summarize_scored_population(scored_entries: Vec<ScoredGenome>) -> PopulationSummary {
        assert!(!scored_entries.is_empty(), "population must not be empty");

        let mut best_idx = 0usize;
        let mut feasible_objectives = Vec::new();
        let mut infeasible = 0usize;
        for (idx, entry) in scored_entries.iter().enumerate() {
            if entry.score.feasible {
                feasible_objectives.push((entry.score.traffic, entry.score.instrs));
            } else {
                infeasible += 1;
            }
            if scored_less(entry, &scored_entries[best_idx]) {
                best_idx = idx;
            }
        }

        let objectives = objective_stats(&mut feasible_objectives);
        let median = objectives.p50;

        PopulationSummary {
            best: scored_entries[best_idx].score.clone(),
            median,
            objectives,
            feasible: feasible_objectives.len(),
            infeasible,
            total: scored_entries.len(),
        }
    }

    fn summarize_scores(scores: Vec<CandidateScore>) -> PopulationSummary {
        assert!(!scores.is_empty(), "score list must not be empty");

        let mut best_idx = 0usize;
        let mut feasible_objectives = Vec::new();
        let mut infeasible = 0usize;
        for (idx, score) in scores.iter().enumerate() {
            if score.feasible {
                feasible_objectives.push((score.traffic, score.instrs));
            } else {
                infeasible += 1;
            }
            if objective_less(score, &scores[best_idx]) {
                best_idx = idx;
            }
        }
        let objectives = objective_stats(&mut feasible_objectives);
        PopulationSummary {
            best: scores[best_idx].clone(),
            median: objectives.p50,
            objectives,
            feasible: feasible_objectives.len(),
            infeasible,
            total: scores.len(),
        }
    }

    fn objective_stats(objectives: &mut Vec<(u64, u64)>) -> ObjectiveStats {
        objectives.sort_unstable();
        ObjectiveStats {
            min: percentile_objective(objectives, 0.00),
            p05: percentile_objective(objectives, 0.05),
            p25: percentile_objective(objectives, 0.25),
            p50: percentile_objective(objectives, 0.50),
            p75: percentile_objective(objectives, 0.75),
            p95: percentile_objective(objectives, 0.95),
            max: percentile_objective(objectives, 1.00),
        }
    }

    fn percentile_objective(objectives: &[(u64, u64)], quantile: f64) -> Option<(u64, u64)> {
        if objectives.is_empty() {
            return None;
        }
        let last = objectives.len() - 1;
        let index = (last as f64 * quantile).round() as usize;
        objectives.get(index.min(last)).copied()
    }

    fn score_genomes_parallel(
        inst: &OracleInstance,
        sites: &[DemandSite],
        entries: Vec<(usize, Genome, Option<MoveFamily>)>,
        workers: usize,
        units: &[Vec<usize>],
    ) -> Vec<ScoredGenome> {
        if entries.is_empty() {
            return Vec::new();
        }

        let worker_count = workers.max(1).min(entries.len());
        let chunk_size = entries.len().div_ceil(worker_count);
        let mut chunks: Vec<Vec<(usize, Genome, Option<MoveFamily>)>> =
            Vec::with_capacity(worker_count);
        let mut current = Vec::with_capacity(chunk_size);
        for entry in entries {
            current.push(entry);
            if current.len() == chunk_size {
                chunks.push(current);
                current = Vec::with_capacity(chunk_size);
            }
        }
        if !current.is_empty() {
            chunks.push(current);
        }

        let mut scored = std::thread::scope(|scope| {
            let handles: Vec<_> = chunks
                .into_iter()
                .map(|chunk| {
                    scope.spawn(move || {
                        chunk
                            .into_iter()
                            .map(|(index, genome, family)| {
                                let score = score_candidate_grouped(inst, sites, &genome, units);
                                ScoredGenome {
                                    index,
                                    genome,
                                    score,
                                    family,
                                }
                            })
                            .collect::<Vec<_>>()
                    })
                })
                .collect();

            handles
                .into_iter()
                .flat_map(|handle| handle.join().expect("scoring worker panicked"))
                .collect::<Vec<_>>()
        });
        scored.sort_by_key(|entry| entry.index);
        scored
    }

    fn objective_less(a: &CandidateScore, b: &CandidateScore) -> bool {
        objective_key(a) < objective_key(b)
    }

    fn objective_key(score: &CandidateScore) -> (u8, u64, u64) {
        (
            if score.feasible { 0 } else { 1 },
            score.traffic,
            score.instrs,
        )
    }

    fn scored_less(a: &ScoredGenome, b: &ScoredGenome) -> bool {
        objective_key(&a.score)
            .cmp(&objective_key(&b.score))
            .then(a.index.cmp(&b.index))
            .is_lt()
    }

    /// Metropolis acceptance for a strictly-worse candidate under simulated annealing.
    /// `delta > 0` is the energy increase (worse primary objective, i.e. read traffic).
    /// Accepts iff `draw < exp(-delta / temperature)`, where `draw` is the optimizer's
    /// RNG sample in `[0, 1)`. At `temperature <= 0` it never accepts a worse candidate,
    /// degenerating to plain hill-climbing.
    fn metropolis_accepts(delta: f64, temperature: f64, draw: f64) -> bool {
        debug_assert!(
            delta > 0.0,
            "metropolis_accepts is only for strictly-worse candidates"
        );
        if temperature <= 0.0 {
            return false;
        }
        draw < (-delta / temperature).exp()
    }

    fn splitmix64(seed: u64) -> u64 {
        let mut z = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Deterministic sample in `[0, 1)` from a seed (top 53 bits of a splitmix64 hash).
    /// Deterministic so the optimizer's annealing stays reproducible across runs.
    fn unit_draw(seed: u64) -> f64 {
        (splitmix64(seed) >> 11) as f64 / (1u64 << 53) as f64
    }

    /// Linear cooling from `SA_INITIAL_TEMPERATURE` at the start of the budget to 0 once
    /// the budget is fully spent, so the search anneals back to pure hill-climbing.
    /// Linear cooling from `SA_INITIAL_TEMPERATURE` at the start of the budget to 0 once
    /// the budget is fully spent, so the search anneals back to pure hill-climbing.
    fn sa_temperature(evals: usize, eval_budget: usize) -> f64 {
        if eval_budget == 0 {
            return 0.0;
        }
        let progress = (evals as f64 / eval_budget as f64).min(1.0);
        SA_INITIAL_TEMPERATURE * (1.0 - progress)
    }

    /// The gentlest feasible neighbor that is strictly worse in primary energy (read
    /// traffic) than `current` — the candidate an uphill SA step would move to. Ties
    /// break on instructions then index. `None` if no such neighbor exists.
    fn best_uphill_neighbor(scored: &[ScoredGenome], current: &CandidateScore) -> Option<usize> {
        scored
            .iter()
            .enumerate()
            .filter(|(_, entry)| entry.score.feasible && entry.score.traffic > current.traffic)
            .min_by(|a, b| {
                (a.1.score.traffic, a.1.score.instrs, a.0)
                    .cmp(&(b.1.score.traffic, b.1.score.instrs, b.0))
            })
            .map(|(idx, _)| idx)
    }

    fn select_optimizer_neighbor(
        scored: &[ScoredGenome],
        current: &CandidateScore,
        plateau_remaining: usize,
    ) -> OptimizerStep {
        let Some((idx, _)) = scored
            .iter()
            .enumerate()
            .filter(|(_, entry)| objective_less(&entry.score, current))
            .min_by(|(_, a), (_, b)| {
                objective_key(&a.score)
                    .cmp(&objective_key(&b.score))
                    .then(a.index.cmp(&b.index))
            })
        else {
            if plateau_remaining == 0 {
                return OptimizerStep::Stop;
            }
            return scored
                .iter()
                .enumerate()
                .find(|(_, entry)| {
                    entry.family.is_some_and(is_cache_move_family)
                        && objective_key(&entry.score) == objective_key(current)
                })
                .map(|(idx, _)| OptimizerStep::Sideways(idx))
                .unwrap_or(OptimizerStep::Stop);
        };

        OptimizerStep::Improving(idx)
    }

    fn is_cache_move_family(family: MoveFamily) -> bool {
        matches!(
            family,
            MoveFamily::AdmitBias | MoveFamily::RecoveryBias | MoveFamily::KeepBias
        )
    }

    /// Budget-proportional beam width: open at most one state per `BEAM_STATE_MIN_BUDGET`
    /// evals (the empirical single-descent convergence budget), capped at
    /// `OPTIMIZER_BEAM_WIDTH`. This makes the beam a strict no-regression generalization
    /// of single-state descent — at budgets that cannot fund breadth it stays width 1.
    fn beam_width_for_budget(eval_budget: usize) -> usize {
        (eval_budget / BEAM_STATE_MIN_BUDGET).clamp(1, OPTIMIZER_BEAM_WIDTH)
    }

    fn optimizer_beam_from_seed_scores(
        mut scored: Vec<ScoredGenome>,
        beam_width: usize,
    ) -> Vec<OptimizerState> {
        assert!(beam_width > 0, "beam width must be positive");
        scored.sort_by(|a, b| {
            objective_key(&a.score)
                .cmp(&objective_key(&b.score))
                .then(a.index.cmp(&b.index))
        });
        let mut states = Vec::with_capacity(beam_width.min(scored.len()));
        for entry in scored {
            if states.len() >= beam_width {
                break;
            }
            // Dedup by decoded order + objective, NOT byte-equal genome: random-key
            // seeds that decode to the same order are redundant starts (identical
            // greedy neighborhood), yet almost never collide bytewise on small root
            // sets. Collapsing them keeps the beam funded with genuinely distinct
            // trajectories.
            if states.iter().any(|state: &OptimizerState| {
                state.score.order == entry.score.order
                    && objective_key(&state.score) == objective_key(&entry.score)
            }) {
                continue;
            }
            states.push(OptimizerState {
                genome: entry.genome,
                score: entry.score,
                plateau_remaining: CACHE_PLATEAU_STEPS,
            });
        }
        states
    }

    fn advance_optimizer_state(
        inst: &OracleInstance,
        sites: &[DemandSite],
        state: &mut OptimizerState,
        eval_budget: usize,
        evals: &mut usize,
        best_genome: &mut Genome,
        best_score: &mut CandidateScore,
        accepted: &mut AcceptedMoves,
        family_stats: &mut MoveFamilyStats,
        units: &[Vec<usize>],
    ) -> bool {
        if *evals >= eval_budget {
            return false;
        }
        // H3: cap each batch to a FIXED branching factor, independent of the remaining
        // eval budget. The root-insert family is O(roots^2); bounding it only by the
        // remaining budget let one advance consume the whole budget at production scale
        // (hundreds of roots), so the search did ~one greedy step. A fixed cap funds
        // many iterations; the beam reuses this per state, so every state inherits it.
        let remaining = (eval_budget - *evals).min(NEIGHBOR_BATCH_CAP);
        let neighbors = neighbor_entries(inst, sites, &state.genome, remaining, units);
        if neighbors.is_empty() {
            return false;
        }
        *evals += neighbors.len();
        let neighbor_scores =
            score_genomes_parallel(inst, sites, neighbors, default_worker_count(), units);
        record_family_improvements(&neighbor_scores, &state.score, family_stats);

        match select_optimizer_neighbor(&neighbor_scores, &state.score, state.plateau_remaining) {
            OptimizerStep::Improving(idx) => {
                let selected = neighbor_scores[idx].clone();
                state.genome = selected.genome;
                state.score = selected.score;
                state.plateau_remaining = CACHE_PLATEAU_STEPS;
                if objective_less(&state.score, best_score) {
                    *best_genome = state.genome.clone();
                    *best_score = state.score.clone();
                }
                if let Some(family) = selected.family {
                    accepted.add(family);
                    family_stats.record_selected(family);
                }
                true
            }
            OptimizerStep::Sideways(idx) => {
                let selected = neighbor_scores[idx].clone();
                state.genome = selected.genome;
                state.score = selected.score;
                state.plateau_remaining = state.plateau_remaining.saturating_sub(1);
                if let Some(family) = selected.family {
                    accepted.add(family);
                    family_stats.record_selected(family);
                }
                true
            }
            OptimizerStep::Stop => {
                // Simulated annealing: rather than abandon a stalled state, accept the
                // gentlest feasible uphill move with Metropolis probability so the search
                // can escape this local optimum. The global best is preserved (this move
                // is strictly worse), and the temperature cools to 0 as the budget is
                // spent, annealing back to hill-climbing — after which this branch stops
                // accepting and the state is dropped.
                let temperature = sa_temperature(*evals, eval_budget);
                let Some(idx) = best_uphill_neighbor(&neighbor_scores, &state.score) else {
                    return false;
                };
                let delta = (neighbor_scores[idx].score.traffic - state.score.traffic) as f64;
                if !metropolis_accepts(delta, temperature, unit_draw(*evals as u64)) {
                    return false;
                }
                let selected = neighbor_scores[idx].clone();
                state.genome = selected.genome;
                state.score = selected.score;
                state.plateau_remaining = CACHE_PLATEAU_STEPS;
                if let Some(family) = selected.family {
                    accepted.add(family);
                    family_stats.record_selected(family);
                }
                true
            }
        }
    }

    fn optimize_from_population(
        inst: &OracleInstance,
        sites: &[DemandSite],
        seeds: Vec<Genome>,
        eval_budget: usize,
    ) -> OptimizerResult {
        // Flat (unconstrained) order — the historical behavior. `&[]` ⇒ no grouping.
        optimize_from_population_grouped(inst, sites, seeds, eval_budget, &[])
    }

    /// Group-atomic variant: the seed genomes are UNIT-KEYED (one ordering key per
    /// unit) and `units` (from `unit_members(relation_units(layer))`) expands them to
    /// occurrence orders, so each gate relation's roots stay contiguous by
    /// construction — the unit is the indivisible scheduling atom. `units == &[]` is
    /// identical to [`optimize_from_population`] (flat, per-occurrence genome).
    pub(crate) fn optimize_from_population_grouped(
        inst: &OracleInstance,
        sites: &[DemandSite],
        seeds: Vec<Genome>,
        eval_budget: usize,
        units: &[Vec<usize>],
    ) -> OptimizerResult {
        assert!(eval_budget > 0, "eval_budget must be positive");

        let seeds = if !seeds.is_empty() {
            seeds
        } else if units.is_empty() {
            vec![Genome::neutral(inst, sites)]
        } else {
            vec![unit_neutral_genome(units.len(), sites)]
        };
        let seed_entries: Vec<_> = seeds
            .into_iter()
            .take(eval_budget)
            .enumerate()
            .map(|(index, genome)| (index, genome, None))
            .collect();
        let mut evals = seed_entries.len();
        let seed_scores =
            score_genomes_parallel(inst, sites, seed_entries, default_worker_count(), units);

        // Initialize a fixed-width beam from the scored seeds (best-objective first,
        // deduped by order+objective). The beam carries several promising states
        // instead of collapsing the population to one greedy incumbent; a lone seed
        // degenerates to a one-state beam (the single-seed call sites are unchanged).
        let mut beam = optimizer_beam_from_seed_scores(seed_scores, beam_width_for_budget(eval_budget));
        let beam_states = beam.len();
        let mut best_genome = beam[0].genome.clone();
        let mut best_score = beam[0].score.clone();
        let mut accepted = AcceptedMoves::default();
        let mut family_stats = MoveFamilyStats::default();
        let mut iterations = 0usize;

        // Round-robin: advance every live state once per round against the shared eval
        // budget and the shared global best. A state that stalls (local optimum /
        // plateau exhausted / empty neighborhood) is dropped so its dead neighborhood
        // is never re-scored. Stop when the budget is spent or every state has stalled.
        while evals < eval_budget && !beam.is_empty() {
            let mut next_beam = Vec::with_capacity(beam.len());
            let mut advanced_any = false;
            for mut state in beam.drain(..) {
                if evals >= eval_budget {
                    next_beam.push(state);
                    continue;
                }
                let before = evals;
                let moved = advance_optimizer_state(
                    inst,
                    sites,
                    &mut state,
                    eval_budget,
                    &mut evals,
                    &mut best_genome,
                    &mut best_score,
                    &mut accepted,
                    &mut family_stats,
                    units,
                );
                if evals > before {
                    iterations += 1;
                }
                if moved {
                    advanced_any = true;
                    next_beam.push(state);
                }
            }
            beam = next_beam;
            if !advanced_any {
                break;
            }
        }

        OptimizerResult {
            best_genome,
            best_score,
            evals,
            iterations,
            beam_states,
            accepted,
            family_stats,
        }
    }

    fn record_family_improvements(
        scored: &[ScoredGenome],
        incumbent: &CandidateScore,
        stats: &mut MoveFamilyStats,
    ) {
        for entry in scored {
            if let Some(family) = entry.family {
                stats.record_candidate(
                    family,
                    &entry.score,
                    objective_less(&entry.score, incumbent),
                );
            }
        }
    }

    fn default_worker_count() -> usize {
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
    }

    fn optimize_smoke_genome(
        inst: &OracleInstance,
        sites: &[DemandSite],
        population_size: usize,
        eval_budget: usize,
    ) -> OptimizerResult {
        let seed_count = eval_budget.min(population_size);
        optimize_from_population(
            inst,
            sites,
            smoke_genome_population(inst, sites, seed_count),
            eval_budget,
        )
    }

    /// Many-root synthetic instance: `r` root Adds over a shared pool of `p` base
    /// reads, so the root-insert move family is O(r^2). With r=64 that is ~4096
    /// candidate moves — larger than the eval budgets below, which is exactly the
    /// production regime where an uncapped batch saturates the budget in one step.
    fn many_root_shared_reads(p: usize, r: usize, budget: usize) -> OracleInstance {
        let mut nodes = Vec::with_capacity(p + r);
        for id in 0..p {
            nodes.push(n(id as u32, NodeKind::Read, 1, true, vec![]));
        }
        let mut roots = Vec::with_capacity(r);
        for i in 0..r {
            let id = (p + i) as u32;
            let children: Vec<u32> = (0..4).map(|k| ((i + k) % p) as u32).collect();
            nodes.push(n(id, NodeKind::Add, 1, false, children));
            roots.push(id);
        }
        OracleInstance {
            budget,
            reloadable_values: vec![],
            roots,
            nodes,
        }
    }

    #[test]
    fn optimizer_iterations_grow_with_eval_budget_on_many_roots() {
        // H3: with the fixed NEIGHBOR_BATCH_CAP a given eval budget funds MANY local-
        // search iterations even when the O(roots^2) root-insert family alone exceeds
        // the budget. Without the cap the first batch saturates the budget and the
        // search degenerates to ~one greedy step regardless of how much budget is left.
        let inst = many_root_shared_reads(12, 64, 4);
        let sites = enumerate_demand_sites(&inst);
        assert!(inst.roots.len() * inst.roots.len() > 3000, "instance must be O(roots^2)-heavy");

        let small = optimize_from_population(&inst, &sites, smoke_genome_population(&inst, &sites, 4), 600);
        let large = optimize_from_population(&inst, &sites, smoke_genome_population(&inst, &sites, 4), 3000);

        eprintln!(
            "[H3] small: iters={} evals={}  large: iters={} evals={}",
            small.iterations, small.evals, large.iterations, large.evals
        );
        assert!(
            small.iterations >= 3,
            "fixed cap must fund several iterations even at a small budget (got {})",
            small.iterations
        );
        assert!(
            large.iterations > small.iterations,
            "iterations must grow with eval budget (small={} large={})",
            small.iterations,
            large.iterations
        );
    }

    #[test]
    fn optimizer_runs_a_beam_over_multiple_distinct_seed_orders() {
        // The optimizer must keep and refine SEVERAL promising seeds, not collapse the
        // population to one greedy incumbent. With two seeds that decode to distinct
        // root orders the beam carries >= 2 live states; a lone seed degenerates to a
        // one-state beam (so the single-seed call sites are unchanged).
        let inst = swap_optimizer_fixture();
        let sites = enumerate_demand_sites(&inst);
        let identity = Genome::neutral(&inst, &sites);
        let mut reversed = Genome::neutral(&inst, &sites);
        reversed.root_order_key = vec![0.75, 0.5, 0.25, 0.0];
        assert_ne!(
            decode_root_order(&inst, &identity),
            decode_root_order(&inst, &reversed),
            "seeds must decode to distinct orders to populate a beam"
        );

        // Budget must clear 2 * BEAM_STATE_MIN_BUDGET so the width policy funds >= 2 states.
        let budget = 4 * BEAM_STATE_MIN_BUDGET;
        let beam = optimize_from_population(&inst, &sites, vec![identity, reversed], budget);
        assert!(
            beam.beam_states >= 2,
            "multiple distinct-order seeds must seed a beam (got {})",
            beam.beam_states
        );

        let solo = optimize_from_population(
            &inst,
            &sites,
            vec![Genome::neutral(&inst, &sites)],
            budget,
        );
        assert_eq!(solo.beam_states, 1);
    }

    #[test]
    fn optimizer_is_deterministic_across_repeated_runs() {
        // Parallel scoring must not leak nondeterminism into selection: identical seeds
        // and budget must yield identical results (objective, order, evals, iterations,
        // beam width, accepted moves) on every run.
        let inst = many_root_shared_reads(12, 64, 4);
        let sites = enumerate_demand_sites(&inst);
        let run = || {
            optimize_from_population(
                &inst,
                &sites,
                smoke_genome_population(&inst, &sites, 6),
                4 * BEAM_STATE_MIN_BUDGET,
            )
        };
        let first = run();
        let second = run();

        assert!(
            first.beam_states >= 2,
            "determinism must be exercised on a real multi-state beam (got {})",
            first.beam_states
        );
        assert_eq!(
            (first.best_score.traffic, first.best_score.instrs),
            (second.best_score.traffic, second.best_score.instrs)
        );
        assert_eq!(first.best_score.order, second.best_score.order);
        assert_eq!(first.evals, second.evals);
        assert_eq!(first.iterations, second.iterations);
        assert_eq!(first.beam_states, second.beam_states);
        assert_eq!(first.accepted, second.accepted);
    }

    fn neighbor_entries(
        inst: &OracleInstance,
        sites: &[DemandSite],
        base: &Genome,
        limit: usize,
        units: &[Vec<usize>],
    ) -> Vec<(usize, Genome, Option<MoveFamily>)> {
        let mut out = Vec::with_capacity(limit);
        // Order moves: when `units` is set the genome is unit-keyed, so a swap/insert/
        // reverse acts on whole units directly (the unit is the scheduling atom — there
        // is nothing to "keep together"). Empty `units` ⇒ the historical per-occurrence
        // (flat) moves.
        if units.is_empty() {
            push_root_swap_neighbors(inst, base, limit, &mut out);
        } else {
            push_unit_swap_neighbors(base, limit, &mut out);
        }
        let cache_slots = reserved_cache_slots(inst, sites, base, limit.saturating_sub(out.len()));
        if units.is_empty() {
            push_root_insert_neighbors(inst, base, limit - cache_slots, &mut out);
            push_root_reverse_neighbors(inst, base, limit - cache_slots, &mut out);
        } else {
            push_unit_insert_neighbors(base, limit - cache_slots, &mut out);
            push_unit_reverse_neighbors(base, limit - cache_slots, &mut out);
        }
        if out.len() < limit {
            let raw_cache_reserve = active_cache_move_families(sites, base).len();
            // Trace reflects the same (flat or unit-keyed) decode the search scores under.
            let (_score, trace) = score_candidate_internal(inst, sites, base, true, units);
            push_trace_guided_cache_neighbors(
                sites,
                base,
                &trace,
                limit.saturating_sub(raw_cache_reserve),
                &mut out,
            );
        }
        push_cache_bias_neighbors_balanced(sites, base, limit, &mut out);
        out
    }

    fn reserved_cache_slots(
        inst: &OracleInstance,
        sites: &[DemandSite],
        base: &Genome,
        remaining: usize,
    ) -> usize {
        let active = active_cache_move_families(sites, base).len();
        if active == 0 || remaining == 0 {
            return 0;
        }
        let fractional_cap = (remaining / 4).max(active).min(remaining);
        let mut slots = fractional_cap.min(active * CACHE_FAMILY_QUOTA);
        if has_root_insert_neighbors(inst) && remaining > active && slots == remaining {
            slots -= 1;
        }
        slots
    }

    fn has_root_insert_neighbors(inst: &OracleInstance) -> bool {
        inst.roots.len() >= 3
    }

    fn active_cache_move_families(sites: &[DemandSite], base: &Genome) -> Vec<MoveFamily> {
        let mut families = Vec::with_capacity(3);
        if !base.cache_priority.is_empty() {
            families.push(MoveFamily::AdmitBias);
        }
        if sites
            .iter()
            .any(|site| site.class == ValueClass::CachedRootOutput)
        {
            families.push(MoveFamily::RecoveryBias);
        }
        if !base.cache_priority.is_empty() {
            families.push(MoveFamily::KeepBias);
        }
        families
    }

    fn push_root_swap_neighbors(
        inst: &OracleInstance,
        base: &Genome,
        limit: usize,
        out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
    ) {
        let order = decode_root_occurrence_order(inst, base);
        for pair in order.windows(2) {
            if out.len() >= limit {
                return;
            }
            let mut candidate = base.clone();
            candidate.root_order_key.swap(pair[0], pair[1]);
            out.push((out.len(), candidate, Some(MoveFamily::RootSwap)));
        }
    }

    fn push_root_insert_neighbors(
        inst: &OracleInstance,
        base: &Genome,
        limit: usize,
        out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
    ) {
        let order = decode_root_occurrence_order(inst, base);
        for from in 0..order.len() {
            for to in 0..order.len() {
                if out.len() >= limit {
                    return;
                }
                if from == to || from.abs_diff(to) == 1 {
                    continue;
                }
                let mut inserted = order.clone();
                let root = inserted.remove(from);
                inserted.insert(to, root);
                out.push((
                    out.len(),
                    genome_with_root_occurrence_order(base, &inserted),
                    Some(MoveFamily::RootInsert),
                ));
            }
        }
    }

    fn genome_with_root_occurrence_order(base: &Genome, order: &[usize]) -> Genome {
        let mut candidate = base.clone();
        let denom = order.len().max(1) as f64;
        for (rank, &root_occurrence) in order.iter().enumerate() {
            candidate.root_order_key[root_occurrence] = rank as f64 / denom;
        }
        candidate
    }

    fn push_root_reverse_neighbors(
        inst: &OracleInstance,
        base: &Genome,
        limit: usize,
        out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
    ) {
        // 2-opt: reverse a contiguous run of the occurrence order. Runs of length 2
        // are skipped because reversing an adjacent pair is exactly a RootSwap move.
        let order = decode_root_occurrence_order(inst, base);
        let n = order.len();
        for i in 0..n {
            for j in (i + 2)..n {
                if out.len() >= limit {
                    return;
                }
                let mut reversed = order.clone();
                reversed[i..=j].reverse();
                out.push((
                    out.len(),
                    genome_with_root_occurrence_order(base, &reversed),
                    Some(MoveFamily::RootReverse),
                ));
            }
        }
    }

    // ── Unit-keyed order moves ────────────────────────────────────────────────
    //
    // The grouped genome carries ONE key per unit, so these are the flat swap/insert/
    // reverse acting on units directly: a unit is the indivisible scheduling atom, so
    // a move relocates a whole unit and members never separate. They mirror the
    // per-occurrence functions above but operate on `decode_unit_order` (a permutation
    // of unit indices) and write back over the unit-keyed genome.

    /// Genome whose unit-key order equals `order` (rank/denom along it).
    fn genome_with_unit_order(base: &Genome, order: &[usize]) -> Genome {
        let mut candidate = base.clone();
        let denom = order.len().max(1) as f64;
        for (rank, &unit) in order.iter().enumerate() {
            candidate.root_order_key[unit] = rank as f64 / denom;
        }
        candidate
    }

    fn push_unit_swap_neighbors(
        base: &Genome,
        limit: usize,
        out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
    ) {
        let order = decode_unit_order(&base.root_order_key);
        for pair in order.windows(2) {
            if out.len() >= limit {
                return;
            }
            let mut candidate = base.clone();
            candidate.root_order_key.swap(pair[0], pair[1]);
            out.push((out.len(), candidate, Some(MoveFamily::RootSwap)));
        }
    }

    fn push_unit_insert_neighbors(
        base: &Genome,
        limit: usize,
        out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
    ) {
        let order = decode_unit_order(&base.root_order_key);
        for from in 0..order.len() {
            for to in 0..order.len() {
                if out.len() >= limit {
                    return;
                }
                if from == to || from.abs_diff(to) == 1 {
                    continue;
                }
                let mut inserted = order.clone();
                let unit = inserted.remove(from);
                inserted.insert(to, unit);
                out.push((
                    out.len(),
                    genome_with_unit_order(base, &inserted),
                    Some(MoveFamily::RootInsert),
                ));
            }
        }
    }

    fn push_unit_reverse_neighbors(
        base: &Genome,
        limit: usize,
        out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
    ) {
        // 2-opt over units: reverse a contiguous run of the unit order (runs of length
        // 2 are skipped — reversing an adjacent pair is exactly a unit swap).
        let order = decode_unit_order(&base.root_order_key);
        let n = order.len();
        for i in 0..n {
            for j in (i + 2)..n {
                if out.len() >= limit {
                    return;
                }
                let mut reversed = order.clone();
                reversed[i..=j].reverse();
                out.push((
                    out.len(),
                    genome_with_unit_order(base, &reversed),
                    Some(MoveFamily::RootReverse),
                ));
            }
        }
    }

    /// Neutral unit-keyed genome: identity unit order, zero cache biases (per site).
    fn unit_neutral_genome(n_units: usize, sites: &[DemandSite]) -> Genome {
        let denom = n_units.max(1) as f64;
        Genome {
            root_order_key: (0..n_units).map(|i| i as f64 / denom).collect(),
            cache_priority: vec![0.0; sites.len()],
        }
    }

    /// Project a per-occurrence (flat) genome to a unit-keyed genome at PARITY: the
    /// per-site cache biases are copied verbatim (identical representation in both
    /// arms), and each unit's order key is the gentlest (minimum) key among its
    /// members, so the unit sorts where the flat order would place its earliest root.
    /// Used to seed the grouped arm from the SAME population as the flat arm, isolating
    /// the move-space effect from seed quality (the seed asymmetry the review flagged).
    pub(crate) fn project_genome_to_units(flat: &Genome, units: &[Vec<usize>]) -> Genome {
        let root_order_key = units
            .iter()
            .map(|members| {
                members
                    .iter()
                    .map(|&occ| flat.root_order_key[occ])
                    .fold(f64::INFINITY, f64::min)
            })
            .collect();
        Genome {
            root_order_key,
            cache_priority: flat.cache_priority.clone(),
        }
    }

    fn push_cache_bias_neighbors_balanced(
        sites: &[DemandSite],
        base: &Genome,
        limit: usize,
        out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
    ) {
        let mut families = active_cache_move_families(sites, base);
        while !families.is_empty() && out.len() < limit {
            let family = families.remove(0);
            let remaining_slots = limit - out.len();
            let family_slots = remaining_slots.div_ceil(families.len() + 1);
            let family_limit = limit.min(out.len() + family_slots);
            push_cache_bias_family_neighbors(sites, base, family, family_limit, out);
        }
    }

    fn push_trace_guided_cache_neighbors(
        sites: &[DemandSite],
        base: &Genome,
        trace: &CacheTrace,
        limit: usize,
        out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
    ) {
        for event in &trace.events {
            if out.len() >= limit {
                return;
            }
            match *event {
                CacheTraceEvent::TrafficRead { .. }
                | CacheTraceEvent::Admit { .. }
                | CacheTraceEvent::NoFutureDemand { .. } => {}
                CacheTraceEvent::PressureReject { value, .. } => {
                    let mut candidate = base.clone();
                    set_admit_bias_for_value(sites, &mut candidate, value, TRACE_GUIDED_BIAS);
                    push_trace_candidate(out, limit, candidate, MoveFamily::AdmitBias);
                }
                CacheTraceEvent::PressureAdmit { site_idx, value } => {
                    let mut admit_candidate = base.clone();
                    set_admit_bias_for_value(
                        sites,
                        &mut admit_candidate,
                        value,
                        -TRACE_GUIDED_BIAS,
                    );
                    push_trace_candidate(out, limit, admit_candidate, MoveFamily::AdmitBias);

                    let mut keep_candidate = base.clone();
                    keep_candidate.cache_priority[site_idx] = TRACE_GUIDED_BIAS;
                    push_trace_candidate(out, limit, keep_candidate, MoveFamily::KeepBias);
                }
                CacheTraceEvent::Evict {
                    victim_last_site,
                    cause: EvictCause::PressureAdmit { .. },
                    ..
                } => {
                    if let Some(victim_site) = victim_last_site {
                        let mut candidate = base.clone();
                        candidate.cache_priority[victim_site] = -TRACE_GUIDED_BIAS;
                        push_trace_candidate(out, limit, candidate, MoveFamily::KeepBias);
                    }
                }
                CacheTraceEvent::Evict { .. } => {}
            }
        }
    }

    fn set_admit_bias_for_value(sites: &[DemandSite], genome: &mut Genome, value: u32, bias: f64) {
        for (idx, site) in sites.iter().enumerate() {
            if site.value == value {
                genome.cache_priority[idx] = bias;
            }
        }
    }

    fn push_trace_candidate(
        out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
        limit: usize,
        candidate: Genome,
        family: MoveFamily,
    ) {
        if out.len() >= limit {
            return;
        }
        if out.iter().any(|(_, genome, _)| *genome == candidate) {
            return;
        }
        out.push((out.len(), candidate, Some(family)));
    }

    fn push_cache_bias_family_neighbors(
        sites: &[DemandSite],
        base: &Genome,
        family: MoveFamily,
        limit: usize,
        out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
    ) {
        match family {
            MoveFamily::AdmitBias => push_admit_bias_neighbors(base, limit, out),
            MoveFamily::RecoveryBias => push_recovery_bias_neighbors(sites, base, limit, out),
            MoveFamily::KeepBias => push_keep_bias_neighbors(base, limit, out),
            MoveFamily::RootSwap | MoveFamily::RootInsert | MoveFamily::RootReverse => {
                panic!("root moves are not cache bias families")
            }
        }
    }

    fn push_admit_bias_neighbors(
        base: &Genome,
        limit: usize,
        out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
    ) {
        for idx in 0..base.cache_priority.len() {
            for delta in [-LOCAL_BIAS_STEP, LOCAL_BIAS_STEP] {
                if out.len() >= limit {
                    return;
                }
                let mut candidate = base.clone();
                candidate.cache_priority[idx] = clamp_bias(candidate.cache_priority[idx] + delta);
                out.push((out.len(), candidate, Some(MoveFamily::AdmitBias)));
            }
        }
    }

    fn push_recovery_bias_neighbors(
        sites: &[DemandSite],
        base: &Genome,
        limit: usize,
        out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
    ) {
        for (idx, site) in sites.iter().enumerate() {
            if site.class != ValueClass::CachedRootOutput {
                continue;
            }
            for delta in [-LOCAL_BIAS_STEP, LOCAL_BIAS_STEP] {
                if out.len() >= limit {
                    return;
                }
                let mut candidate = base.clone();
                candidate.cache_priority[idx] = clamp_bias(candidate.cache_priority[idx] + delta);
                out.push((out.len(), candidate, Some(MoveFamily::RecoveryBias)));
            }
        }
    }

    fn push_keep_bias_neighbors(
        base: &Genome,
        limit: usize,
        out: &mut Vec<(usize, Genome, Option<MoveFamily>)>,
    ) {
        for idx in 0..base.cache_priority.len() {
            for delta in [-LOCAL_BIAS_STEP, LOCAL_BIAS_STEP] {
                if out.len() >= limit {
                    return;
                }
                let mut candidate = base.clone();
                candidate.cache_priority[idx] =
                    clamp_bias(candidate.cache_priority[idx] + delta);
                out.push((out.len(), candidate, Some(MoveFamily::KeepBias)));
            }
        }
    }

    fn try_root_swap_neighbors(
        inst: &OracleInstance,
        sites: &[DemandSite],
        base: &Genome,
        eval_budget: usize,
        evals: &mut usize,
        best_genome: &mut Genome,
        best_score: &mut CandidateScore,
        best_family: &mut Option<MoveFamily>,
    ) {
        let order = decode_root_occurrence_order(inst, base);
        for pair in order.windows(2) {
            if *evals >= eval_budget {
                return;
            }
            let mut candidate = base.clone();
            candidate.root_order_key.swap(pair[0], pair[1]);
            score_neighbor(
                inst,
                sites,
                candidate,
                MoveFamily::RootSwap,
                evals,
                best_genome,
                best_score,
                best_family,
            );
        }
    }

    fn try_bias_neighbors(
        inst: &OracleInstance,
        sites: &[DemandSite],
        base: &Genome,
        eval_budget: usize,
        evals: &mut usize,
        best_genome: &mut Genome,
        best_score: &mut CandidateScore,
        best_family: &mut Option<MoveFamily>,
    ) {
        for idx in 0..base.cache_priority.len() {
            for delta in [-LOCAL_BIAS_STEP, LOCAL_BIAS_STEP] {
                if *evals >= eval_budget {
                    return;
                }
                let mut candidate = base.clone();
                candidate.cache_priority[idx] = clamp_bias(candidate.cache_priority[idx] + delta);
                score_neighbor(
                    inst,
                    sites,
                    candidate,
                    MoveFamily::AdmitBias,
                    evals,
                    best_genome,
                    best_score,
                    best_family,
                );
            }
        }

        for (idx, site) in sites.iter().enumerate() {
            if site.class != ValueClass::CachedRootOutput {
                continue;
            }
            for delta in [-LOCAL_BIAS_STEP, LOCAL_BIAS_STEP] {
                if *evals >= eval_budget {
                    return;
                }
                let mut candidate = base.clone();
                candidate.cache_priority[idx] = clamp_bias(candidate.cache_priority[idx] + delta);
                score_neighbor(
                    inst,
                    sites,
                    candidate,
                    MoveFamily::RecoveryBias,
                    evals,
                    best_genome,
                    best_score,
                    best_family,
                );
            }
        }

        for idx in 0..base.cache_priority.len() {
            for delta in [-LOCAL_BIAS_STEP, LOCAL_BIAS_STEP] {
                if *evals >= eval_budget {
                    return;
                }
                let mut candidate = base.clone();
                candidate.cache_priority[idx] =
                    clamp_bias(candidate.cache_priority[idx] + delta);
                score_neighbor(
                    inst,
                    sites,
                    candidate,
                    MoveFamily::KeepBias,
                    evals,
                    best_genome,
                    best_score,
                    best_family,
                );
            }
        }
    }

    fn score_neighbor(
        inst: &OracleInstance,
        sites: &[DemandSite],
        genome: Genome,
        family: MoveFamily,
        evals: &mut usize,
        best_genome: &mut Genome,
        best_score: &mut CandidateScore,
        best_family: &mut Option<MoveFamily>,
    ) {
        let score = score_candidate(inst, sites, &genome);
        *evals += 1;
        if objective_less(&score, best_score) {
            *best_genome = genome;
            *best_score = score;
            *best_family = Some(family);
        }
    }

    fn smoke_genome_population(
        inst: &OracleInstance,
        sites: &[DemandSite],
        total: usize,
    ) -> Vec<Genome> {
        let mut genomes = Vec::with_capacity(total);
        if total == 0 {
            return genomes;
        }

        genomes.push(Genome::neutral(inst, sites));
        if genomes.len() < total {
            let mut reversed = Genome::neutral(inst, sites);
            let n = reversed.root_order_key.len();
            let denom = n.max(1) as f64;
            for (idx, key) in reversed.root_order_key.iter_mut().enumerate() {
                *key = (n - 1 - idx) as f64 / denom;
            }
            genomes.push(reversed);
        }
        if genomes.len() < total {
            genomes.push(reuse_weighted_smoke_genome(inst, sites));
        }

        while genomes.len() < total {
            genomes.push(deterministic_smoke_genome(
                inst,
                sites,
                (genomes.len() - 3) as u64,
            ));
        }
        genomes
    }

    /// Like `smoke_genome_population` but the random tail is seeded from `run_offset`, so
    /// distinct runs explore distinct random starts (the structured neutral / reversed /
    /// reuse-weighted anchors are kept in every run). `run_offset == 0` reproduces
    /// `smoke_genome_population` exactly. Used to measure between-run search variance.
    pub(crate) fn seeded_smoke_population(
        inst: &OracleInstance,
        sites: &[DemandSite],
        total: usize,
        run_offset: u64,
    ) -> Vec<Genome> {
        let mut genomes = Vec::with_capacity(total);
        if total == 0 {
            return genomes;
        }
        genomes.push(Genome::neutral(inst, sites));
        if genomes.len() < total {
            let mut reversed = Genome::neutral(inst, sites);
            let n = reversed.root_order_key.len();
            let denom = n.max(1) as f64;
            for (idx, key) in reversed.root_order_key.iter_mut().enumerate() {
                *key = (n - 1 - idx) as f64 / denom;
            }
            genomes.push(reversed);
        }
        if genomes.len() < total {
            genomes.push(reuse_weighted_smoke_genome(inst, sites));
        }
        while genomes.len() < total {
            let seed = run_offset
                .wrapping_mul(0x9E37_79B9_7F4A_7C15)
                .wrapping_add((genomes.len() - 3) as u64);
            genomes.push(deterministic_smoke_genome(inst, sites, seed));
        }
        genomes
    }

    struct SmokeRng {
        state: u64,
    }

    impl SmokeRng {
        fn new(seed: u64) -> Self {
            Self {
                state: seed ^ 0x9e37_79b9_7f4a_7c15,
            }
        }

        fn next_u64(&mut self) -> u64 {
            self.state = self
                .state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.state
        }

        fn next_unit(&mut self) -> f64 {
            let mantissa = self.next_u64() >> 11;
            mantissa as f64 * (1.0 / ((1u64 << 53) as f64))
        }

        fn next_signed(&mut self) -> f64 {
            self.next_unit() * 2.0 - 1.0
        }
    }

    fn run_smoke(label: &str, inst: &OracleInstance, sites: &[DemandSite]) {
        run_smoke_with_params(label, inst, sites, 1000, 10_000);
    }

    fn run_smoke_with_params(
        label: &str,
        inst: &OracleInstance,
        sites: &[DemandSite],
        population_size: usize,
        eval_budget: usize,
    ) {
        use std::time::Instant;

        assert!(!inst.roots.is_empty());
        assert!(!sites.is_empty());
        assert!(population_size > 0);
        assert!(eval_budget > 0);

        let baseline = score_candidate(inst, sites, &Genome::neutral(inst, sites));

        let mut swapped_genome = Genome::neutral(inst, sites);
        if swapped_genome.root_order_key.len() >= 2 {
            swapped_genome.root_order_key.swap(0, 1);
        }
        let swapped = score_candidate(inst, sites, &swapped_genome);

        let start = Instant::now();
        let population = score_population_parallel(
            inst,
            sites,
            smoke_genome_population(inst, sites, population_size),
            default_worker_count(),
        );
        let elapsed = start.elapsed();
        let best = (population.best.traffic, population.best.instrs);
        let median = population
            .median
            .expect("smoke test must produce at least one feasible candidate");
        let avg_ns = elapsed.as_nanos() / population.total as u128;

        let opt_start = Instant::now();
        let optimized = optimize_smoke_genome(inst, sites, population_size, eval_budget);
        let opt_elapsed = opt_start.elapsed();
        let opt_avg_ns = opt_elapsed.as_nanos() / optimized.evals as u128;

        eprintln!(
            "[META] {label} nodes={} roots={} sites={} population={} eval_budget={} baseline={:?}/{} swapped={:?}/{} feasible={}/{} best={best:?} median={median:?} init=[{}] infeasible={} avg={}ns/candidate best_order={:?} opt_best={:?}/{} opt_evals={} opt_avg={}ns/eval opt_moves=(swap:{},insert:{},admit:{},recovery:{},keep:{}) opt_family=[{}] opt_admit=[{}] opt_order={:?}",
            inst.nodes.len(),
            inst.roots.len(),
            sites.len(),
            population_size,
            eval_budget,
            (baseline.traffic, baseline.instrs),
            if baseline.feasible { "feasible" } else { "infeasible" },
            (swapped.traffic, swapped.instrs),
            if swapped.feasible { "feasible" } else { "infeasible" },
            population.feasible,
            population.total,
            format_objective_stats(population.objectives),
            population.infeasible,
            avg_ns,
            population.best.order,
            (optimized.best_score.traffic, optimized.best_score.instrs),
            if optimized.best_score.feasible {
                "feasible"
            } else {
                "infeasible"
            },
            optimized.evals,
            opt_avg_ns,
            optimized.accepted.root_swaps,
            optimized.accepted.root_inserts,
            optimized.accepted.admit_bias,
            optimized.accepted.recovery_bias,
            optimized.accepted.keep_after_use_bias,
            format_family_stats(optimized.family_stats),
            format_admit_stats(optimized.best_score.admit_stats),
            optimized.best_score.order,
        );

        assert_eq!(population.total, population_size);
        assert!(population.feasible > 0);
        assert!(optimized.best_score.feasible);
    }

    struct CompactSmoke {
        baseline: CandidateScore,
        best: CandidateScore,
        initial_objectives: ObjectiveStats,
        optimized: OptimizerResult,
        final_states: FinalStateSummary,
        feasible: usize,
        total: usize,
        infeasible: usize,
        avg_ns: u128,
        opt_avg_ns: u128,
    }

    struct FinalStateSummary {
        objectives: ObjectiveStats,
        best: CandidateScore,
        feasible: usize,
        total: usize,
        infeasible: usize,
        evals: usize,
        avg_ns: u128,
        family_stats: MoveFamilyStats,
    }

    fn compact_smoke(
        inst: &OracleInstance,
        sites: &[DemandSite],
        population_size: usize,
        eval_budget: usize,
        final_starts: usize,
        final_eval_budget: usize,
    ) -> CompactSmoke {
        use std::time::Instant;

        let baseline = score_candidate(inst, sites, &Genome::neutral(inst, sites));

        let start = Instant::now();
        let population = score_population_parallel(
            inst,
            sites,
            smoke_genome_population(inst, sites, population_size),
            default_worker_count(),
        );
        let elapsed = start.elapsed();

        let opt_start = Instant::now();
        let optimized = optimize_smoke_genome(inst, sites, population_size, eval_budget);
        let opt_elapsed = opt_start.elapsed();
        let opt_avg_ns = opt_elapsed.as_nanos() / optimized.evals.max(1) as u128;
        let final_states = final_state_summary(
            inst,
            sites,
            final_starts,
            final_eval_budget,
            optimized.best_score.clone(),
        );

        CompactSmoke {
            baseline,
            best: population.best,
            initial_objectives: population.objectives,
            optimized,
            final_states,
            feasible: population.feasible,
            total: population.total,
            infeasible: population.infeasible,
            avg_ns: elapsed.as_nanos() / population.total as u128,
            opt_avg_ns,
        }
    }

    fn final_state_summary(
        inst: &OracleInstance,
        sites: &[DemandSite],
        starts: usize,
        eval_budget: usize,
        incumbent: CandidateScore,
    ) -> FinalStateSummary {
        use std::time::Instant;

        assert!(starts > 0, "final state starts must be positive");
        assert!(eval_budget > 0, "final state eval budget must be positive");

        let mut scores = Vec::with_capacity(starts + 1);
        scores.push(incumbent);
        let mut evals = 0usize;
        let mut family_stats = MoveFamilyStats::default();
        let start_time = Instant::now();
        for genome in smoke_genome_population(inst, sites, starts) {
            let optimized = optimize_from_population(inst, sites, vec![genome], eval_budget);
            evals += optimized.evals;
            family_stats.merge(optimized.family_stats);
            scores.push(optimized.best_score);
        }
        let elapsed = start_time.elapsed();
        let summary = summarize_scores(scores);

        FinalStateSummary {
            objectives: summary.objectives,
            best: summary.best,
            feasible: summary.feasible,
            total: summary.total,
            infeasible: summary.infeasible,
            evals,
            avg_ns: elapsed.as_nanos() / evals.max(1) as u128,
            family_stats,
        }
    }

    fn format_objective_stats(stats: ObjectiveStats) -> String {
        format!(
            "min={} p05={} p25={} p50={} p75={} p95={} max={}",
            format_objective(stats.min),
            format_objective(stats.p05),
            format_objective(stats.p25),
            format_objective(stats.p50),
            format_objective(stats.p75),
            format_objective(stats.p95),
            format_objective(stats.max),
        )
    }

    fn format_objective(objective: Option<(u64, u64)>) -> String {
        match objective {
            Some(objective) => format!("{objective:?}"),
            None => "NA".to_owned(),
        }
    }

    fn format_family_stats(stats: MoveFamilyStats) -> String {
        format!(
            "sw={} ins={} a={} rec={} k={}",
            format_family_counters(stats.root_swaps),
            format_family_counters(stats.root_inserts),
            format_family_counters(stats.admit_bias),
            format_family_counters(stats.recovery_bias),
            format_family_counters(stats.keep_after_use_bias),
        )
    }

    fn format_family_counters(counters: MoveFamilyCounters) -> String {
        format!(
            "{}/{}/{}/best={}/imp={}",
            counters.tried,
            counters.improving,
            counters.selected,
            format_objective(counters.best),
            format_objective(counters.best_improving)
        )
    }

    fn format_admit_stats(stats: AdmitStats) -> String {
        format!(
            "resident={} no_future={} free={} reject={} no_victim={} pressure_ok={}",
            stats.already_resident,
            stats.no_future_demand,
            stats.free_capacity,
            stats.pressure_rejected,
            stats.pressure_no_victim,
            stats.pressure_admitted,
        )
    }

    const ALL_22_L0_FIXTURES: &[&str] = &[
        "add_sub_lui_auipc_mop_layout_gkr.json",
        "bigint_with_extended_control_layout_gkr.json",
        "blake2_g_function_layout_gkr.json",
        "blake2_with_extended_control_layout_gkr.json",
        "inits_and_teardowns_preprocessed_layout_gkr.json",
        "jump_branch_slt_layout_gkr.json",
        "keccak_special5_layout_gkr.json",
        "mem_subword_only_layout_gkr.json",
        "mem_word_only_layout_gkr.json",
        "shift_binop_layout_gkr.json",
        "unsigned_mul_div_layout_gkr.json",
        "add_sub_lui_auipc_mop_layout_no_caches_gkr.json",
        "bigint_with_extended_control_layout_no_caches_gkr.json",
        "blake2_g_function_layout_no_caches_gkr.json",
        "blake2_with_extended_control_layout_no_caches_gkr.json",
        "inits_and_teardowns_layout_no_caches_gkr.json",
        "jump_branch_slt_layout_no_caches_gkr.json",
        "keccak_special5_layout_no_caches_gkr.json",
        "mem_subword_only_layout_no_caches_gkr.json",
        "mem_word_only_layout_no_caches_gkr.json",
        "shift_binop_layout_no_caches_gkr.json",
        "unsigned_mul_div_layout_no_caches_gkr.json",
    ];

    // ── Shared cache-reuse helpers (Part B: same-layer cache reuse is a shared ExprId) ──
    //
    // A cache root's attribute-model identity (Stage-1 lowering): a `Cache` materialize
    // with no claim. Same-layer reuse of a cache value is NOT a `Source(Prior)` any more —
    // a consumer references the cache value's shared `expr: ExprId` directly, so the value
    // is "reused" by a root iff that root's expr cone reaches the cache root's `expr`.

    /// Map each cache root's shared `expr` → its `RootId`.
    fn cache_expr_to_root(
        layer: &cs::gkr_compiler::dag_ir::DagLayer,
    ) -> std::collections::HashMap<cs::gkr_compiler::dag_ir::ExprId, cs::gkr_compiler::dag_ir::RootId>
    {
        use cs::gkr_compiler::dag_ir::{RootId, SinkInfo, SinkKind};
        (0..layer.roots.len() as u32)
            .map(RootId)
            .filter(|&rid| {
                let r = &layer.roots[rid.0 as usize];
                matches!(&r.materialize, Some(SinkInfo { kind: SinkKind::Cache { .. }, .. }))
                    && r.claim.is_none()
            })
            .map(|rid| (layer.roots[rid.0 as usize].expr, rid))
            .collect()
    }

    /// Walk the expr cone of `top` and return the set of cache-root `RootId`s whose shared
    /// `expr` is reached (descending through reached cache exprs too — shared chains).
    fn cache_roots_in_cone(
        layer: &cs::gkr_compiler::dag_ir::DagLayer,
        top: cs::gkr_compiler::dag_ir::ExprId,
        cache_expr_to_root: &std::collections::HashMap<
            cs::gkr_compiler::dag_ir::ExprId,
            cs::gkr_compiler::dag_ir::RootId,
        >,
    ) -> std::collections::BTreeSet<cs::gkr_compiler::dag_ir::RootId> {
        use cs::gkr_compiler::dag_ir::{Expr, ExprId, SourceKind};
        let mut hit = std::collections::BTreeSet::new();
        let mut visited: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
        let mut stack: Vec<ExprId> = vec![top];
        while let Some(eid) = stack.pop() {
            if !visited.insert(eid.0) {
                continue;
            }
            if let Some(&rid) = cache_expr_to_root.get(&eid) {
                hit.insert(rid);
            }
            match &layer.exprs[eid.0 as usize] {
                Expr::Source(sid) => {
                    if let SourceKind::LookupValue { query, .. } =
                        &layer.sources[sid.0 as usize].kind
                    {
                        stack.push(*query);
                    }
                }
                Expr::Add(ch) | Expr::Mul(ch) => stack.extend(ch.iter().copied()),
            }
        }
        hit
    }

    #[derive(Clone, Copy, Debug, Default)]
    struct ReachableReadStats {
        read_sources: usize,
        read_source_cells: usize,
        read_places: usize,
        read_place_cells: usize,
        // Part B: "prior" now means distinct same-layer cache VALUES reached in the
        // materialized-root cones (their shared `expr` appears in a cone), with the
        // value's width summed in cells. (There is no `Source(Prior)` any more.)
        prior_sources: usize,
        prior_cells: usize,
    }

    fn reachable_read_stats(
        layer: &cs::gkr_compiler::dag_ir::DagLayer,
        cross: &std::collections::HashMap<
            cs::gkr_compiler::dag_ir::ReadPlace,
            cs::gkr_compiler::dag_ir::FieldKind,
        >,
    ) -> ReachableReadStats {
        use cs::gkr_compiler::dag_ir::{Expr, ExprId, SourceKind};
        use gkr_eval_isa::fwd::compile::expr_operand_field;
        use gkr_eval_isa::fwd::isa::OperandField;
        use std::collections::{HashMap, HashSet};

        // Cache-value identity: each cache root's shared `expr` (Part B replaces `Prior`).
        let cache_roots = cache_expr_to_root(layer);

        let mut seen_expr = HashSet::new();
        let mut read_sources = HashSet::new();
        let mut read_places = HashMap::new();
        // Distinct same-layer cache VALUES (by cache-root expr) reached in the cones.
        let mut prior_values: HashSet<u32> = HashSet::new();
        let mut read_source_cells = 0usize;
        let mut read_place_cells = 0usize;
        let mut prior_cells = 0usize;
        let mut stack: Vec<_> = layer
            .roots
            .iter()
            // Materialized roots (Output + Cache); skip claim-only Constraint roots.
            .filter_map(|root| root.materialize.is_some().then_some(root.expr.0))
            .collect();

        while let Some(eid) = stack.pop() {
            if !seen_expr.insert(eid) {
                continue;
            }
            if layer.resolutions.contains_key(&ExprId(eid)) {
                continue;
            }
            // A reached cache-root `expr` is a same-layer cache value (the old `Prior`).
            if cache_roots.contains_key(&ExprId(eid)) && prior_values.insert(eid) {
                let cells = if expr_operand_field(layer, ExprId(eid), cross) == OperandField::Ext {
                    4
                } else {
                    1
                };
                prior_cells += cells;
            }
            match &layer.exprs[eid as usize] {
                Expr::Source(source_id) => {
                    let cells =
                        if expr_operand_field(layer, ExprId(eid), cross) == OperandField::Ext {
                            4
                        } else {
                            1
                        };
                    match &layer.sources[source_id.0 as usize].kind {
                        SourceKind::Read { place } => {
                            if read_sources.insert(source_id.0) {
                                read_source_cells += cells;
                            }
                            if read_places.insert(place.clone(), cells).is_none() {
                                read_place_cells += cells;
                            }
                        }
                        SourceKind::VirtualSetup { .. }
                        | SourceKind::Constant { .. }
                        | SourceKind::Challenge { .. }
                        | SourceKind::LookupValue { .. } => {}
                    }
                }
                Expr::Add(children) | Expr::Mul(children) => {
                    stack.extend(children.iter().map(|child| child.0));
                }
            }
        }

        ReachableReadStats {
            read_sources: read_sources.len(),
            read_source_cells,
            read_places: read_places.len(),
            read_place_cells,
            prior_sources: prior_values.len(),
            prior_cells,
        }
    }

    #[test]
    fn corpus_fixture_list_has_expected_22_layouts() {
        assert_eq!(ALL_22_L0_FIXTURES.len(), 22);
    }

    #[test]
    #[ignore = "research smoke: loads a real fixture and scores 1000 candidates"]
    fn real_cluster_smoke_scores_many_candidates() {
        use crate::s3_gap::instance::extract_instance;

        let (dag, _artifact, _cross) =
            crate::load_layer_source("add_sub_lui_auipc_mop_layout_gkr.json");
        let layer = &dag.layers[0];
        let candidates = crate::sweet_spot_clusters(layer, 1, 2, 12);
        let cluster = candidates
            .first()
            .expect("expected at least one small add_sub L0 cluster");
        let inst = extract_instance(&cluster.layer, &cluster.cross, crate::REAL_BUDGET);
        let sites = enumerate_demand_sites(&inst);
        run_smoke(
            &format!("real-cluster seed={:?}", cluster.seed),
            &inst,
            &sites,
        );
    }

    #[test]
    #[ignore = "research smoke: loads full add_sub L0 and scores 1000 candidates"]
    fn real_full_l0_smoke_scores_many_candidates() {
        use crate::s3_gap::instance::extract_instance;

        let (dag, _artifact, cross) =
            crate::load_layer_source("add_sub_lui_auipc_mop_layout_gkr.json");
        let inst = extract_instance(&dag.layers[0], &cross, crate::REAL_BUDGET);
        let sites = enumerate_demand_sites(&inst);
        run_smoke("real-full-add_sub-L0", &inst, &sites);
    }

    #[test]
    #[ignore = "wide research smoke: loads full add_sub L0 and scores 10000 candidates"]
    fn real_full_l0_wide_smoke_scores_many_candidates() {
        use crate::s3_gap::instance::extract_instance;

        let (dag, _artifact, cross) =
            crate::load_layer_source("add_sub_lui_auipc_mop_layout_gkr.json");
        let inst = extract_instance(&dag.layers[0], &cross, crate::REAL_BUDGET);
        let sites = enumerate_demand_sites(&inst);
        run_smoke_with_params("real-full-add_sub-L0-wide", &inst, &sites, 10_000, 50_000);
    }

    #[test]
    #[ignore = "research smoke: scores metaheuristic optimizer across all 22 L0 layouts"]
    fn real_all_22_l0_smoke_scores_candidates() {
        use crate::s3_gap::instance::extract_instance;

        const POPULATION: usize = 1000;
        const EVAL_BUDGET: usize = 10_000;
        const FINAL_STARTS: usize = 16;
        const FINAL_EVAL_BUDGET: usize = 2_000;

        let mut loaded = 0usize;
        let mut scored = 0usize;
        println!(
            "[META-CORPUS] population={POPULATION} eval_budget={EVAL_BUDGET} final_starts={FINAL_STARTS} final_eval_budget={FINAL_EVAL_BUDGET} budget={}",
            crate::REAL_BUDGET
        );
        for &fixture in ALL_22_L0_FIXTURES {
            let name = fixture
                .trim_end_matches("_layout_gkr.json")
                .trim_end_matches("_layout_no_caches_gkr.json");
            let flavor = if fixture.contains("no_caches") {
                "no-cache"
            } else {
                "cache"
            };
            let label = format!("{name}/{flavor}");
            let Some((layer, cross)) = crate::try_load_l0(fixture) else {
                println!("[META-CORPUS] {label:<52} LOAD_FAILED");
                continue;
            };
            loaded += 1;
            let inst = extract_instance(&layer, &cross, crate::REAL_BUDGET);
            let sites = enumerate_demand_sites(&inst);
            if inst.roots.is_empty() || sites.is_empty() {
                println!(
                    "[META-CORPUS] {label:<52} nodes={:<5} roots={:<4} sites={:<4} SKIP",
                    inst.nodes.len(),
                    inst.roots.len(),
                    sites.len(),
                );
                continue;
            }

            let smoke = compact_smoke(
                &inst,
                &sites,
                POPULATION,
                EVAL_BUDGET,
                FINAL_STARTS,
                FINAL_EVAL_BUDGET,
            );
            scored += 1;
            println!(
                "[META-CORPUS] {label:<52} nodes={:<5} roots={:<4} sites={:<4} feasible={:>4}/{:<4} base={:?}/{} init=[{}] opt={:?}/{} evals={:<5} moves=(sw:{},ins:{},a:{},rec:{},k:{}) fam=[{}] opt_admit=[{}] final_feasible={:>3}/{:<3} final=[{}] final_best={:?} final_fam=[{}] final_admit=[{}] final_evals={:<5} final_avg={}ns avg={}ns opt_avg={}ns infeasible={} final_infeasible={}",
                inst.nodes.len(),
                inst.roots.len(),
                sites.len(),
                smoke.feasible,
                smoke.total,
                (smoke.baseline.traffic, smoke.baseline.instrs),
                if smoke.baseline.feasible { "feasible" } else { "infeasible" },
                format_objective_stats(smoke.initial_objectives),
                (smoke.optimized.best_score.traffic, smoke.optimized.best_score.instrs),
                if smoke.optimized.best_score.feasible { "feasible" } else { "infeasible" },
                smoke.optimized.evals,
                smoke.optimized.accepted.root_swaps,
                smoke.optimized.accepted.root_inserts,
                smoke.optimized.accepted.admit_bias,
                smoke.optimized.accepted.recovery_bias,
                smoke.optimized.accepted.keep_after_use_bias,
                format_family_stats(smoke.optimized.family_stats),
                format_admit_stats(smoke.optimized.best_score.admit_stats),
                smoke.final_states.feasible,
                smoke.final_states.total,
                format_objective_stats(smoke.final_states.objectives),
                (smoke.final_states.best.traffic, smoke.final_states.best.instrs),
                format_family_stats(smoke.final_states.family_stats),
                format_admit_stats(smoke.final_states.best.admit_stats),
                smoke.final_states.evals,
                smoke.final_states.avg_ns,
                smoke.avg_ns,
                smoke.opt_avg_ns,
                smoke.infeasible,
                smoke.final_states.infeasible,
            );
        }

        assert_eq!(loaded, ALL_22_L0_FIXTURES.len());
        assert!(scored > 0);
    }

    #[test]
    #[ignore = "research stats: counts unique RAM sources in all 22 L0 layouts"]
    fn real_all_22_l0_ram_source_counts() {
        println!(
            "[RAM-SOURCES] counts are reachable reads; source ids are DAG ids, places are physical RAM locations; cells use base=1 ext=4"
        );
        for &fixture in ALL_22_L0_FIXTURES {
            let name = fixture
                .trim_end_matches("_layout_gkr.json")
                .trim_end_matches("_layout_no_caches_gkr.json");
            let flavor = if fixture.contains("no_caches") {
                "no-cache"
            } else {
                "cache"
            };
            let label = format!("{name}/{flavor}");
            let Some((layer, cross)) = crate::try_load_l0(fixture) else {
                println!("[RAM-SOURCES] {label:<52} LOAD_FAILED");
                continue;
            };

            let stats = reachable_read_stats(&layer, &cross);

            println!(
                "[RAM-SOURCES] {label:<52} read_src={:>4} read_src_cells={:>4} read_place={:>4} read_place_cells={:>4} prior={:>4} prior_cells={:>4} src_total={:>4} src_total_cells={:>4}",
                stats.read_sources,
                stats.read_source_cells,
                stats.read_places,
                stats.read_place_cells,
                stats.prior_sources,
                stats.prior_cells,
                stats.read_sources + stats.prior_sources,
                stats.read_source_cells + stats.prior_cells,
            );
        }
    }

    fn all_fit_budget(inst: &OracleInstance) -> usize {
        inst.nodes
            .iter()
            .map(|node| node.width as usize)
            .sum::<usize>()
            .max(1)
    }

    #[test]
    #[ignore = "research invariant: with all values resident, every candidate reads each physical input once"]
    fn real_all_22_l0_all_fit_budget_reads_equal_physical_inputs() {
        use crate::s3_gap::instance::extract_instance;

        const POPULATION: usize = 1000;

        let mut checked = 0usize;
        let fixture_filter = std::env::var("ALL_FIT_FIXTURE_FILTER").ok();
        for &fixture in ALL_22_L0_FIXTURES {
            let name = fixture
                .trim_end_matches("_layout_gkr.json")
                .trim_end_matches("_layout_no_caches_gkr.json");
            let flavor = if fixture.contains("no_caches") {
                "no-cache"
            } else {
                "cache"
            };
            let label = format!("{name}/{flavor}");
            if let Some(filter) = &fixture_filter {
                if !label.contains(filter) && !fixture.contains(filter) {
                    continue;
                }
            }
            let Some((layer, cross)) = crate::try_load_l0(fixture) else {
                println!("[ALL-FIT] {label:<52} LOAD_FAILED");
                continue;
            };
            let expected = reachable_read_stats(&layer, &cross).read_place_cells as u64;
            let mut inst = extract_instance(&layer, &cross, crate::REAL_BUDGET);
            inst.budget = all_fit_budget(&inst);
            let sites = enumerate_demand_sites(&inst);
            if inst.roots.is_empty() || sites.is_empty() {
                println!(
                    "[ALL-FIT] {label:<52} expected={expected:<4} budget={:<5} nodes={:<5} roots={:<4} sites={:<4} SKIP",
                    inst.budget,
                    inst.nodes.len(),
                    inst.roots.len(),
                    sites.len(),
                );
                continue;
            }

            let mut min_traffic = u64::MAX;
            let mut max_traffic = 0u64;
            for (idx, genome) in smoke_genome_population(&inst, &sites, POPULATION)
                .into_iter()
                .enumerate()
            {
                let (score, trace) = score_candidate_with_trace(&inst, &sites, &genome);
                min_traffic = min_traffic.min(score.traffic);
                max_traffic = max_traffic.max(score.traffic);
                assert!(
                    score.feasible,
                    "{label}: candidate {idx} is infeasible under all-fit budget {}",
                    inst.budget
                );
                let duplicate_reads = duplicate_traffic_reads(&trace);
                let duplicate_details = duplicate_read_site_details(&trace, &sites, &genome, &inst);
                assert_eq!(
                    score.traffic, expected,
                    "{label}: candidate {idx} traffic {} != unique physical input cells {expected}; duplicate reads={duplicate_reads:?}; details={duplicate_details:?}",
                    score.traffic,
                );
            }
            println!(
                "[ALL-FIT] {label:<52} expected={expected:<4} min={min_traffic:<4} max={max_traffic:<4} budget={:<5}",
                inst.budget,
            );
            checked += 1;
        }

        if fixture_filter.is_none() {
            assert_eq!(checked, ALL_22_L0_FIXTURES.len());
        } else {
            assert!(checked > 0, "ALL_FIT_FIXTURE_FILTER matched no fixtures");
        }
    }

    /// REPORT: per-fixture best read-count budget sweep. For each L0 fixture, run the
    /// optimizer at cell budgets 8, 12, 16, … and record the BEST discovered traffic
    /// (read count) at each budget, stopping once it converges to the all-resident floor
    /// (`read_place_cells`, printed on every row) or the all-fit budget is reached.
    /// `INF` = no feasible candidate at that budget (cone peak exceeds it).
    #[test]
    #[ignore = "report: per-fixture best read-count budget sweep (8,12,16,… vs floor)"]
    fn real_all_22_l0_budget_sweep_best_read_counts() {
        use crate::s3_gap::instance::extract_instance;

        const POPULATION: usize = 200;
        const EVAL_BUDGET: usize = 2_000;
        const START: usize = 8;
        const STEP: usize = 4;
        const MAX_STEPS: usize = 64;

        for &fixture in ALL_22_L0_FIXTURES {
            let name = fixture
                .trim_end_matches("_layout_gkr.json")
                .trim_end_matches("_layout_no_caches_gkr.json");
            let flavor = if fixture.contains("no_caches") {
                "no-cache"
            } else {
                "cache"
            };
            let label = format!("{name}/{flavor}");
            let Some((layer, cross)) = crate::try_load_l0(fixture) else {
                println!("[SWEEP] {label:<52} LOAD_FAILED");
                continue;
            };
            let floor = reachable_read_stats(&layer, &cross).read_place_cells as u64;
            let mut inst = extract_instance(&layer, &cross, crate::REAL_BUDGET);
            let sites = enumerate_demand_sites(&inst);
            if inst.roots.is_empty() || sites.is_empty() {
                println!("[SWEEP] {label:<52} floor={floor:<4} SKIP (no roots/sites)");
                continue;
            }
            let all_fit = all_fit_budget(&inst);

            let mut points = Vec::new();
            let mut budget = START;
            let mut converged_at: Option<usize> = None;
            for _ in 0..MAX_STEPS {
                inst.budget = budget;
                let opt = optimize_from_population(
                    &inst,
                    &sites,
                    smoke_genome_population(&inst, &sites, POPULATION),
                    EVAL_BUDGET,
                );
                if opt.best_score.feasible {
                    points.push(format!("b{budget}={}", opt.best_score.traffic));
                    if opt.best_score.traffic <= floor {
                        converged_at = Some(budget);
                        break;
                    }
                } else {
                    points.push(format!("b{budget}=INF"));
                }
                if budget >= all_fit {
                    break;
                }
                budget += STEP;
            }
            let conv = converged_at
                .map(|b| b.to_string())
                .unwrap_or_else(|| "—".to_string());
            println!(
                "[SWEEP] {label:<52} floor={floor:<4} all_fit={all_fit:<5} converged@{conv:<4} | {}",
                points.join(" ")
            );
        }
    }

    /// REPORT: distance-from-floor across the full (fixture × layer × budget) grid — the
    /// principled quality metric (neutral-baseline `total_gap` is only a regression guard).
    /// For every layer of every fixture, sweep cell budgets at 25/50/75/100% of that
    /// layer's all-fit capacity and report `residual = optimized − floor` (and relative
    /// %). `floor` = `read_place_cells`; the scorer is `>= floor` always and `== floor` at
    /// all-fit, so residual ≥ 0 and `residual == 0` means the layer hit its optimum.
    /// `INF` = infeasible at that budget (cone peak exceeds it). The aggregate is the
    /// total residual at 50% capacity over feasible layers — the headline "how far above
    /// optimal, under moderate pressure, across the whole corpus" number.
    #[test]
    #[ignore = "report: distance-from-floor across all layers × budgets (quality metric)"]
    fn real_all_layers_distance_from_floor_sweep() {
        use crate::s3_gap::instance::extract_instance;

        const POPULATION: usize = 200;
        const EVAL_BUDGET: usize = 4_000;
        // Absolute cell-budget ladder anchored at the production budget (REAL_BUDGET=16).
        // The meaningful "enough cache" size is the CONVERGENCE budget (where residual hits
        // 0 = the optimal schedule's peak live-set): ~48 for add_sub cache, ~192 for bigint
        // cache, >256 for blake2_ext cache; no-cache layouts converge by b24. Production b16
        // is below that for the wide CACHE layouts, so b16 is the tight band where residual
        // lives. NB: all_fit_budget is Σ of ALL node widths (every input AND intermediate) —
        // a loose ceiling where nothing is ever evicted, NOT the working set; it overstates
        // residency need, so it is used here only as a stop bound. Stop at convergence.
        const BUDGETS: [usize; 9] = [16, 24, 32, 48, 64, 96, 128, 192, 256];

        let mut total_residual_at_real = 0u64;
        let mut feasible_at_real = 0usize;
        let mut converged_layers = 0usize;
        let mut total_layers = 0usize;

        for &fixture in ALL_22_L0_FIXTURES {
            let name = fixture
                .trim_end_matches("_layout_gkr.json")
                .trim_end_matches("_layout_no_caches_gkr.json");
            let flavor = if fixture.contains("no_caches") {
                "no-cache"
            } else {
                "cache"
            };
            let (dag, _artifact, cross) = crate::load_layer_source(fixture);
            for (layer_idx, layer) in dag.layers.iter().enumerate() {
                let floor = reachable_read_stats(layer, &cross).read_place_cells as u64;
                let mut inst = extract_instance(layer, &cross, crate::REAL_BUDGET);
                let sites = enumerate_demand_sites(&inst);
                if inst.roots.is_empty() || sites.is_empty() {
                    continue;
                }
                total_layers += 1;
                let all_fit = all_fit_budget(&inst);
                let population = smoke_genome_population(&inst, &sites, POPULATION);

                let mut points = Vec::new();
                let mut converged = false;
                for &budget in &BUDGETS {
                    if budget > all_fit {
                        break;
                    }
                    inst.budget = budget;
                    let opt =
                        optimize_from_population(&inst, &sites, population.clone(), EVAL_BUDGET);
                    if opt.best_score.feasible {
                        let residual = opt.best_score.traffic.saturating_sub(floor);
                        let rel = if floor > 0 {
                            100.0 * residual as f64 / floor as f64
                        } else {
                            0.0
                        };
                        points.push(format!(
                            "b{budget}={}(+{residual},{rel:.0}%)",
                            opt.best_score.traffic
                        ));
                        if budget == crate::REAL_BUDGET {
                            total_residual_at_real += residual;
                            feasible_at_real += 1;
                        }
                        if residual == 0 {
                            converged = true;
                            break;
                        }
                    } else {
                        points.push(format!("b{budget}=INF"));
                    }
                }
                if converged {
                    converged_layers += 1;
                }
                println!(
                    "[FLOORDIST] {name:<34} {flavor:<8} L{layer_idx:<2} floor={floor:<4} all_fit={all_fit:<5} | {}",
                    points.join(" ")
                );
            }
        }

        println!(
            "[FLOORDIST][SUMMARY] layers={total_layers} converged_to_floor={converged_layers} \
             total_residual@REAL_BUDGET={total_residual_at_real} (over {feasible_at_real} layers feasible @ {})",
            crate::REAL_BUDGET
        );
    }

    /// REPORT: heavy statistical sweep over (fixture × flavor × layer × cache-budget),
    /// emitting one JSON row per cell. Each cell runs the optimizer `SWEEP_RUNS` times with
    /// distinct seeded populations (`seeded_smoke_population` per run) for BOTH the flat
    /// (per-occurrence) and the unit-keyed (group-atomic, parity-seeded) arm, so the row
    /// carries the full per-run traffic arrays — the between-run variance the artifact plots.
    /// Budgets start at 8, step by 4, capped per layer at all_fit; a layer stops once the
    /// best-of-runs of BOTH arms reaches the floor. Rows are prefixed `SWEEPROW `.
    ///
    /// Compute is intentionally heavy; tune via env (defaults in parens):
    ///   SWEEP_RUNS (4)  SWEEP_POP (1000)  SWEEP_EVALS (12000)  SWEEP_BUDGET_MAX (64)
    #[test]
    #[ignore = "report: heavy multi-run (layer × budget) sweep, flat vs unit-keyed; JSON rows"]
    fn real_sweep_all_layers_budgets_grouped_vs_flat() {
        // extract_instance now models cache values as intra-unit inline intermediates
        // (the default), a no-op for no-cache fixtures — the single correct model.
        use crate::s3_gap::instance::{extract_instance, relation_units};

        let env_usize = |key: &str, default: usize| {
            std::env::var(key).ok().and_then(|v| v.parse().ok()).unwrap_or(default)
        };
        let runs = env_usize("SWEEP_RUNS", 4).max(1);
        let population = env_usize("SWEEP_POP", 1000).max(1);
        let eval_budget = env_usize("SWEEP_EVALS", 12_000).max(1);
        let budget_max = env_usize("SWEEP_BUDGET_MAX", 64);
        let budgets: Vec<usize> = (8..=budget_max).step_by(4).collect();
        eprintln!(
            "[SWEEP] runs={runs} population={population} eval_budget={eval_budget} \
             budgets={budgets:?}"
        );

        let json_arr = |xs: &[u64]| -> String {
            let body: Vec<String> = xs.iter().map(|x| x.to_string()).collect();
            format!("[{}]", body.join(","))
        };
        let json_bool_arr = |xs: &[bool]| -> String {
            let body: Vec<String> = xs.iter().map(|x| x.to_string()).collect();
            format!("[{}]", body.join(","))
        };

        for &fixture in ALL_22_L0_FIXTURES {
            let name = fixture
                .trim_end_matches("_layout_gkr.json")
                .trim_end_matches("_layout_no_caches_gkr.json");
            let flavor = if fixture.contains("no_caches") {
                "no-cache"
            } else {
                "cache"
            };
            let (dag, _artifact, cross) = crate::load_layer_source(fixture);
            for (layer_idx, layer) in dag.layers.iter().enumerate() {
                let floor = reachable_read_stats(layer, &cross).read_place_cells as u64;
                let mut inst = extract_instance(layer, &cross, crate::REAL_BUDGET);
                let sites = enumerate_demand_sites(&inst);
                if inst.roots.is_empty() || sites.is_empty() {
                    continue;
                }
                let all_fit = all_fit_budget(&inst);
                let unit_of = relation_units(layer);
                assert_eq!(
                    unit_of.len(),
                    inst.roots.len(),
                    "{name}/{flavor} L{layer_idx}: relation_units must align with roots"
                );
                let units = unit_members(&unit_of);
                let multi = units.iter().filter(|m| m.len() > 1).count();
                // DAG ceiling (budget-independent): the no-caching max reads. Every
                // feasible result must satisfy floor <= traffic <= ceiling.
                let ceiling = no_cache_ceiling(&inst, &sites);

                // Per-run seeded populations (shared across budgets so each run is one
                // coherent random start); grouped pop is the parity projection of the flat.
                let flat_pops: Vec<Vec<Genome>> = (0..runs)
                    .map(|r| seeded_smoke_population(&inst, &sites, population, r as u64))
                    .collect();
                let unit_pops: Vec<Vec<Genome>> = flat_pops
                    .iter()
                    .map(|pop| pop.iter().map(|g| project_genome_to_units(g, &units)).collect())
                    .collect();

                for &budget in &budgets {
                    if budget > all_fit {
                        break;
                    }
                    inst.budget = budget;
                    let mut flat_runs = Vec::with_capacity(runs);
                    let mut flat_feas = Vec::with_capacity(runs);
                    let mut grouped_runs = Vec::with_capacity(runs);
                    let mut grouped_feas = Vec::with_capacity(runs);
                    for r in 0..runs {
                        let flat = optimize_from_population(
                            &inst,
                            &sites,
                            flat_pops[r].clone(),
                            eval_budget,
                        );
                        let grouped = optimize_from_population_grouped(
                            &inst,
                            &sites,
                            unit_pops[r].clone(),
                            eval_budget,
                            &units,
                        );
                        flat_runs.push(flat.best_score.traffic);
                        flat_feas.push(flat.best_score.feasible);
                        grouped_runs.push(grouped.best_score.traffic);
                        grouped_feas.push(grouped.best_score.feasible);
                    }
                    // SANITY: floor <= feasible traffic <= no_cache_ceiling, both arms.
                    for (t, f) in flat_runs.iter().zip(&flat_feas).chain(grouped_runs.iter().zip(&grouped_feas)) {
                        if *f {
                            assert!(
                                *t >= floor && *t <= ceiling,
                                "{name}/{flavor} L{layer_idx} b{budget}: traffic {t} outside \
                                 [floor {floor}, ceiling {ceiling}] — scorer/search broken"
                            );
                        }
                    }
                    println!(
                        "SWEEPROW {{\"name\":\"{name}\",\"flavor\":\"{flavor}\",\"layer\":{layer_idx},\
                         \"roots\":{},\"units\":{},\"multi\":{multi},\"floor\":{floor},\
                         \"ceiling\":{ceiling},\"all_fit\":{all_fit},\"budget\":{budget},\
                         \"flat_runs\":{},\"flat_feas\":{},\"grouped_runs\":{},\"grouped_feas\":{}}}",
                        inst.roots.len(),
                        units.len(),
                        json_arr(&flat_runs),
                        json_bool_arr(&flat_feas),
                        json_arr(&grouped_runs),
                        json_bool_arr(&grouped_feas),
                    );
                    // best-of-runs convergence (only over feasible runs).
                    let best_feasible = |runs: &[u64], feas: &[bool]| -> Option<u64> {
                        runs.iter()
                            .zip(feas)
                            .filter(|(_, f)| **f)
                            .map(|(&t, _)| t)
                            .min()
                    };
                    let fb = best_feasible(&flat_runs, &flat_feas);
                    let gb = best_feasible(&grouped_runs, &grouped_feas);
                    if fb == Some(floor) && gb == Some(floor) {
                        break; // both arms converged to floor; higher budgets stay there
                    }
                }
            }
        }
        println!("SWEEPDONE");
    }

    /// INVESTIGATION: are `Cache`-sink roots reused only WITHIN their own layer (via
    /// `Prior`), or are some read by a LATER layer (via `Read{LayerOutput}`)? Only
    /// intra-layer cache values can be modeled as "materialize after first evaluation"
    /// (a non-root shared intermediate); a cross-layer cache value is a genuine exported
    /// output and must stay a root. Scans the whole DAG of every cache fixture.
    #[test]
    #[ignore = "investigate: are Cache roots intra-layer (Prior) or cross-layer (LayerOutput)?"]
    fn cache_root_locality_census() {
        use cs::gkr_compiler::dag_ir::{ReadPlace, RootId, SinkInfo, SinkKind, SourceKind};
        use std::collections::BTreeSet;

        let mut tot_cache = 0usize;
        let mut tot_intra = 0usize;
        let mut tot_cross = 0usize;
        let mut tot_both = 0usize;
        let mut tot_orphan = 0usize;
        for &fixture in ALL_22_L0_FIXTURES {
            if fixture.contains("no_caches") {
                continue;
            }
            let name = fixture.trim_end_matches("_layout_gkr.json");
            let (dag, _artifact, _cross) = crate::load_layer_source(fixture);

            // Global set of (layer, offset) read by some LATER layer via LayerOutput.
            let mut layer_output_reads: BTreeSet<(usize, usize)> = BTreeSet::new();
            for layer in &dag.layers {
                for s in &layer.sources {
                    if let SourceKind::Read {
                        place: ReadPlace::LayerOutput { layer: l, offset: o },
                    } = &s.kind
                    {
                        layer_output_reads.insert((*l, *o));
                    }
                }
            }

            let mut f_cache = 0usize;
            let mut f_intra = 0usize;
            let mut f_cross = 0usize;
            let mut f_both = 0usize;
            let mut f_orphan = 0usize;
            let mut inner_cross = 0usize;
            let mut inner_total = 0usize;
            for layer in dag.layers.iter() {
                // Part B: intra-layer cache REUSE is a shared `ExprId` — a cache value is
                // reused intra-layer iff its `expr` is reached by SOME OTHER root's cone.
                // Build the set of cache RootIds whose value is so reused.
                let cache_roots = cache_expr_to_root(layer);
                let mut reused: BTreeSet<RootId> = BTreeSet::new();
                for (ri, root) in layer.roots.iter().enumerate() {
                    for cache_rid in cache_roots_in_cone(layer, root.expr, &cache_roots) {
                        // Skip a cache root trivially reaching its own expr (that is not reuse).
                        if cache_rid.0 as usize != ri {
                            reused.insert(cache_rid);
                        }
                    }
                }
                for (rid, root) in layer.roots.iter().enumerate() {
                    // Cache root: a `Cache` materialize with no claim.
                    let Some(SinkInfo { kind: SinkKind::Cache { layer: cl, offset: co }, .. }) =
                        (if root.claim.is_none() { root.materialize.as_ref() } else { None })
                    else {
                        // Inner materialize → cross-layer read tally (claim or not).
                        if let Some(SinkInfo { kind: SinkKind::Inner { layer: il, offset: io }, .. }) =
                            root.materialize.as_ref()
                        {
                            inner_total += 1;
                            if layer_output_reads.contains(&(*il, *io)) {
                                inner_cross += 1;
                            }
                        }
                        continue;
                    };
                    f_cache += 1;
                    let intra = reused.contains(&RootId(rid as u32));
                    let cross = layer_output_reads.contains(&(*cl, *co));
                    match (intra, cross) {
                        (true, false) => f_intra += 1,
                        (false, true) => f_cross += 1,
                        (true, true) => f_both += 1,
                        (false, false) => f_orphan += 1,
                    }
                }
            }
            println!(
                "[CACHE-LOC] {name:<40} cache={f_cache:<4} intra-only={f_intra:<4} \
                 cross-only={f_cross:<3} both={f_both:<3} orphan={f_orphan:<3} | \
                 inner={inner_total} inner_cross_read={inner_cross}"
            );
            tot_cache += f_cache;
            tot_intra += f_intra;
            tot_cross += f_cross;
            tot_both += f_both;
            tot_orphan += f_orphan;
        }
        println!(
            "[CACHE-LOC][SUMMARY] cache_roots={tot_cache} intra-only={tot_intra} \
             cross-only={tot_cross} both={tot_both} orphan={tot_orphan} \
             => cache-as-non-root is {} (cross+both must be 0)",
            if tot_cross + tot_both == 0 { "SAFE for all" } else { "NOT universally safe" }
        );
    }

    /// DEMONSTRATION + SANITY (a): does modeling cache values as intra-unit inline
    /// intermediates (not scheduling roots) collapse the cache layout to its no-cache
    /// forward cost? For each circuit (L0) compares THREE extractions — cache-as-root
    /// (current), cache-materialized (new), and no-cache — on roots, reads, floor, the
    /// DAG ceiling, and the optimized forward traffic at REAL_BUDGET. Asserts every
    /// optimized result is within `[floor, no_cache_ceiling]` (the hard sanity bound) and
    /// that materialization does not change the read-leaf set. Tunable via SWEEP_EVALS.
    #[test]
    #[ignore = "demo: cache-materialized collapses to no-cache forward cost + ceiling sanity"]
    fn cache_materialized_collapse_demo() {
        use crate::s3_gap::instance::{extract_instance, extract_instance_cache_as_root};
        let pop = std::env::var("SWEEP_POP").ok().and_then(|v| v.parse().ok()).unwrap_or(600);
        let evals = std::env::var("SWEEP_EVALS").ok().and_then(|v| v.parse().ok()).unwrap_or(8_000);

        let read_cells = |inst: &OracleInstance| -> u64 {
            inst.nodes.iter().filter(|n| n.real_dram).map(|n| n.width as u64).sum()
        };
        let run = |inst: &OracleInstance| -> (u64, bool, u64) {
            let sites = enumerate_demand_sites(inst);
            let ceiling = no_cache_ceiling(inst, &sites);
            let opt = optimize_from_population(
                inst,
                &sites,
                smoke_genome_population(inst, &sites, pop),
                evals,
            );
            (opt.best_score.traffic, opt.best_score.feasible, ceiling)
        };

        println!("[COLLAPSE] evals={evals} pop={pop} (opt @ REAL_BUDGET={})", crate::REAL_BUDGET);
        for &fixture in ALL_22_L0_FIXTURES {
            if fixture.contains("no_caches") {
                continue;
            }
            let name = fixture.trim_end_matches("_layout_gkr.json");
            let nc_fixture = fixture
                .replace("_preprocessed_layout_gkr.json", "_layout_no_caches_gkr.json")
                .replace("_layout_gkr.json", "_layout_no_caches_gkr.json");
            let (Some((cl, cc)), Some((nl, nc))) =
                (crate::try_load_l0(fixture), crate::try_load_l0(&nc_fixture))
            else {
                println!("[COLLAPSE] {name:<40} LOAD_FAILED");
                continue;
            };
            let floor_c = reachable_read_stats(&cl, &cc).read_place_cells as u64;
            let floor_n = reachable_read_stats(&nl, &nc).read_place_cells as u64;
            let i_root = extract_instance_cache_as_root(&cl, &cc, crate::REAL_BUDGET);
            let i_mat = extract_instance(&cl, &cc, crate::REAL_BUDGET);
            let i_nc = extract_instance(&nl, &nc, crate::REAL_BUDGET);
            if i_mat.roots.is_empty() {
                continue;
            }

            // Materialization must not change the read-leaf set.
            assert_eq!(
                read_cells(&i_root),
                read_cells(&i_mat),
                "{name}: cache materialization changed reads"
            );

            let (o_root, f_root, ceil_root) = run(&i_root);
            let (o_mat, f_mat, ceil_mat) = run(&i_mat);
            let (o_nc, f_nc, ceil_nc) = run(&i_nc);

            // SANITY: every optimized result lies within [floor, no_cache_ceiling].
            for (lbl, o, feas, ceil, fl) in [
                ("cache-root", o_root, f_root, ceil_root, floor_c),
                ("cache-mat", o_mat, f_mat, ceil_mat, floor_c),
                ("no-cache", o_nc, f_nc, ceil_nc, floor_n),
            ] {
                if feas {
                    assert!(o >= fl, "{name}/{lbl}: opt {o} < floor {fl}");
                    assert!(o <= ceil, "{name}/{lbl}: opt {o} > ceiling {ceil} (scorer/search broken)");
                }
            }
            println!(
                "[COLLAPSE] {name:<40} roots[root/mat/nc]={}/{}/{} reads[root/mat/nc]={}/{}/{} \
                 floor[c/nc]={floor_c}/{floor_n} opt[root/mat/nc]={o_root}/{o_mat}/{o_nc} \
                 mat-vs-nc_gap={}",
                i_root.roots.len(),
                i_mat.roots.len(),
                i_nc.roots.len(),
                read_cells(&i_root),
                read_cells(&i_mat),
                read_cells(&i_nc),
                o_mat as i64 - o_nc as i64,
            );
        }
    }

    /// INVESTIGATION: forward/backward root taxonomy. The forward cost model only
    /// schedules `Root::Output` cones. The BACKWARD pass (sumcheck) consumes the
    /// claim-bearing roots (those with a `RootOrigin` / in `BatchingOrder`) and the
    /// constraints (`Root::Constraint`). This census shows, per cache fixture: how the
    /// retained-for-backward values appear as roots, whether any Cache root is itself
    /// claim-bearing (it must not be), and how many claim roots are PURE backward (no
    /// intra-forward Prior consumer) — i.e. "computed in forward, used only in backward".
    #[test]
    #[ignore = "investigate: forward/backward root taxonomy (claims vs cache vs constraints)"]
    fn forward_backward_root_taxonomy() {
        use cs::gkr_compiler::dag_ir::{Expr, ExprId, SinkInfo, SinkKind};
        use std::collections::BTreeSet;

        for &fixture in ALL_22_L0_FIXTURES {
            if fixture.contains("no_caches") {
                continue;
            }
            let name = fixture.trim_end_matches("_layout_gkr.json");
            let (dag, _a, _c) = crate::load_layer_source(fixture);
            let mut out_total = 0usize;
            let mut claim = 0usize; // claim-bearing root (sumcheck claim)
            let mut cache = 0usize; // Cache materialize, no claim
            let mut inner = 0usize;
            let mut cache_and_claim = 0usize; // MUST be 0 (orthogonal attributes)
            let mut claim_no_intra = 0usize; // claim with no intra-layer (shared-ExprId) reuse
            let mut constraints = 0usize;
            for layer in &dag.layers {
                // Part B: intra-layer reuse is a shared `ExprId`. A root's value is reused
                // intra-forward iff its `expr` is reached by ANOTHER root's cone. Map each
                // root's `expr` to its index, then mark reuse.
                let expr_to_root: std::collections::HashMap<ExprId, usize> = layer
                    .roots
                    .iter()
                    .enumerate()
                    .map(|(i, r)| (r.expr, i))
                    .collect();
                let mut reused: BTreeSet<usize> = BTreeSet::new();
                for (ri, root) in layer.roots.iter().enumerate() {
                    let mut visited: BTreeSet<u32> = BTreeSet::new();
                    let mut stack = vec![root.expr];
                    let mut first = true;
                    while let Some(eid) = stack.pop() {
                        if !visited.insert(eid.0) {
                            continue;
                        }
                        // The root's own top expr is not "reuse"; descend past it.
                        if !first {
                            if let Some(&owner) = expr_to_root.get(&eid) {
                                if owner != ri {
                                    reused.insert(owner);
                                }
                            }
                        }
                        first = false;
                        if let Expr::Add(ch) | Expr::Mul(ch) = &layer.exprs[eid.0 as usize] {
                            stack.extend(ch.iter().copied());
                        }
                    }
                }
                for (rid, root) in layer.roots.iter().enumerate() {
                    if root.materialize.is_none() {
                        // Claim-only (Constraint) root.
                        constraints += 1;
                        continue;
                    }
                    out_total += 1;
                    let is_claim = root.claim.is_some();
                    let is_cache = matches!(
                        &root.materialize,
                        Some(SinkInfo { kind: SinkKind::Cache { .. }, .. })
                    ) && root.claim.is_none();
                    if is_claim {
                        claim += 1;
                        if !reused.contains(&rid) {
                            claim_no_intra += 1;
                        }
                    }
                    if is_cache {
                        cache += 1;
                    }
                    if matches!(
                        &root.materialize,
                        Some(SinkInfo { kind: SinkKind::Inner { .. }, .. })
                    ) {
                        inner += 1;
                    }
                    if is_claim && is_cache {
                        cache_and_claim += 1;
                    }
                }
            }
            println!(
                "[ROOT-TAX] {name:<40} out={out_total:<4} claim={claim:<4} cache={cache:<4} \
                 inner={inner:<4} constraints={constraints:<4} cache∩claim={cache_and_claim} \
                 claim_pure_backward(no_intra)={claim_no_intra}"
            );
        }
    }

    /// REPORT: precise structural comparison of the cache vs no-cache DAG for each circuit
    /// (L0). The no-cache DAG is the existence proof of what the SAME computation costs
    /// without materialization, so it bounds whether the cache layout's b16 residual is
    /// structural. Per flavor we compute, straight from the DAG: `floor` (each leaf read
    /// once = budget→∞ limit), `all_recompute` (Σ over demand sites of the value's
    /// recompute-from-base traffic = budget→0 limit, no caching/sharing), root & site
    /// counts, and `opt@16` (optimizer at the production budget). Reading: `opt@16` must
    /// lie in `[floor, all_recompute]`. If cache `opt@16 > all_recompute`, the optimizer
    /// is doing WORSE than always-recompute → pure search failure. If the two flavors'
    /// `all_recompute` match but cache `opt@16` ≫ no-cache `opt@16`, the recompute schedule
    /// that no-cache found is expressible on the cache DAG and the optimizer simply missed
    /// it (search). If cache `all_recompute` is structurally higher, the gap is real.
    #[test]
    #[ignore = "report: cache-vs-no-cache DAG structural comparison (floor/all-recompute/opt@16)"]
    fn cache_vs_no_cache_dag_structural_comparison() {
        use crate::s3_gap::instance::extract_instance;
        const POPULATION: usize = 200;
        const EVAL_BUDGET: usize = 4_000;

        // (floor, all_recompute, n_roots, n_sites, opt@REAL_BUDGET)
        fn structural(fixture: &str) -> Option<(u64, u64, usize, usize, u64)> {
            let (layer, cross) = crate::try_load_l0(fixture)?;
            let floor = reachable_read_stats(&layer, &cross).read_place_cells as u64;
            let inst = extract_instance(&layer, &cross, crate::REAL_BUDGET);
            let sites = enumerate_demand_sites(&inst);
            if inst.roots.is_empty() || sites.is_empty() {
                return None;
            }
            let all_recompute: u64 = sites
                .iter()
                .map(|s| recompute_traffic_for(&inst, s.value))
                .sum();
            let opt = optimize_from_population(
                &inst,
                &sites,
                smoke_genome_population(&inst, &sites, POPULATION),
                EVAL_BUDGET,
            );
            let opt_at_real = if opt.best_score.feasible {
                opt.best_score.traffic
            } else {
                u64::MAX
            };
            Some((floor, all_recompute, inst.roots.len(), sites.len(), opt_at_real))
        }

        for &fixture in ALL_22_L0_FIXTURES {
            if fixture.contains("no_caches") {
                continue;
            }
            let name = fixture.trim_end_matches("_layout_gkr.json");
            // Derive the no-cache twin. The `_preprocessed` cache variant (inits) maps to a
            // no-cache fixture WITHOUT `_preprocessed`, so strip that first; otherwise the
            // plain suffix swap applies. (Avoids silently dropping inits from the pairing.)
            let nc_fixture = fixture
                .replace("_preprocessed_layout_gkr.json", "_layout_no_caches_gkr.json")
                .replace("_layout_gkr.json", "_layout_no_caches_gkr.json");
            let Some((cf, car, croots, csites, copt)) = structural(fixture) else {
                continue;
            };
            let Some((nf, nar, nroots, nsites, nopt)) = structural(&nc_fixture) else {
                println!("[STRUCT] {name:<34} no-cache fixture MISSING");
                continue;
            };
            let verdict = if copt > car {
                "SEARCH-FAIL(opt>all_recompute)"
            } else if car <= nar.saturating_add(nar / 20) && copt > nopt.saturating_add(nopt / 20) {
                "SEARCH(recompute-path-exists)"
            } else if car > nar.saturating_add(nar / 5) {
                "STRUCTURAL(cache recomputes more)"
            } else {
                "mixed/converged"
            };
            println!(
                "[STRUCT] {name:<32} cache[floor={cf} opt={copt} allrc={car} roots={croots} sites={csites}] \
                 nocache[floor={nf} opt={nopt} allrc={nar} roots={nroots} sites={nsites}] => {verdict}"
            );
        }
    }

    /// REPORT: expression-level structural diff between the cache and no-cache layout of
    /// each circuit (L0). The cache layout factors shared subexpressions into `Cache`-sink
    /// roots, reused by consumers via `Source(Prior{id})`; the no-cache layout inlines
    /// them. The decisive quantity is each cache root's FAN-OUT (# of Prior reuses): with
    /// low fan-out a lifetime-aware ORDER can place the reuse right after production (no
    /// residency, no re-read), so the cache residual would be search-addressable, not
    /// structural. High/spread fan-out forces a value to stay live across many consumers.
    #[test]
    #[ignore = "report: expression-level cache-vs-no-cache diff (cache-root fan-out)"]
    fn cache_vs_no_cache_expression_divergence() {
        use cs::gkr_compiler::dag_ir::{DagLayer, RootId, SinkInfo, SinkKind, SourceKind};
        use std::collections::{BTreeMap, BTreeSet};

        struct Stat {
            exprs: usize,
            reads: usize,
            priors: usize,
            inner: usize,
            cache: usize,
            export: usize,
            constraint: usize,
            fanout_hist: BTreeMap<usize, usize>,
            max_fanout: usize,
            // fan-IN: distinct cached values a single consumer root reaches at once
            max_fanin: usize,
            fanin_hist: BTreeMap<usize, usize>,
        }

        fn analyze(layer: &DagLayer) -> Stat {
            let reads = layer
                .sources
                .iter()
                .filter(|s| matches!(s.kind, SourceKind::Read { .. }))
                .count();
            // Part B: a cache value's reuse is a shared `ExprId`. Build cache-expr → RootId,
            // then count, per cache root, the number of OTHER root cones that reach it
            // (fan-out) and, per root, the distinct cache values reached (fan-in).
            let cache_roots = cache_expr_to_root(layer);
            let mut fanout: BTreeMap<u32, usize> = BTreeMap::new(); // cache RootId → consumer count
            let mut priors = 0usize; // total cache-reuse edges (≈ old Prior-source count)
            let (mut inner, mut cache, mut export, mut constraint) = (0usize, 0, 0, 0);
            let mut fanout_hist: BTreeMap<usize, usize> = BTreeMap::new();
            let mut max_fanout = 0usize;
            let mut fanin_hist: BTreeMap<usize, usize> = BTreeMap::new();
            let mut max_fanin = 0usize;
            // Initialize fan-out 0 for every cache root so even unreached caches show.
            for (&_expr, &rid) in cache_roots.iter() {
                fanout.entry(rid.0).or_insert(0);
            }
            for (rid, root) in layer.roots.iter().enumerate() {
                if let Some(SinkInfo { kind, .. }) = &root.materialize {
                    match kind {
                        SinkKind::Inner { .. } => inner += 1,
                        SinkKind::Export { .. } => export += 1,
                        SinkKind::Scratch { .. } => {}
                        SinkKind::Cache { .. } if root.claim.is_none() => cache += 1,
                        SinkKind::Cache { .. } => {}
                    }
                } else {
                    constraint += 1;
                }
                // fan-in: distinct cache values reached in this root's cone (excluding the
                // root trivially reaching its own cache expr).
                let mut caches_in_cone: BTreeSet<RootId> = BTreeSet::new();
                for cache_rid in cache_roots_in_cone(layer, root.expr, &cache_roots) {
                    if cache_rid.0 as usize != rid {
                        caches_in_cone.insert(cache_rid);
                        *fanout.entry(cache_rid.0).or_insert(0) += 1;
                        priors += 1;
                    }
                }
                let fi = caches_in_cone.len();
                if fi > 0 {
                    *fanin_hist.entry(fi).or_default() += 1;
                    max_fanin = max_fanin.max(fi);
                }
            }
            for (_rid, f) in fanout.iter() {
                *fanout_hist.entry(*f).or_default() += 1;
                max_fanout = max_fanout.max(*f);
            }
            Stat {
                exprs: layer.exprs.len(),
                reads,
                priors,
                inner,
                cache,
                export,
                constraint,
                fanout_hist,
                max_fanout,
                max_fanin,
                fanin_hist,
            }
        }

        for &fixture in ALL_22_L0_FIXTURES {
            if fixture.contains("no_caches") {
                continue;
            }
            let name = fixture.trim_end_matches("_layout_gkr.json");
            // Derive the no-cache twin. The `_preprocessed` cache variant (inits) maps to a
            // no-cache fixture WITHOUT `_preprocessed`, so strip that first; otherwise the
            // plain suffix swap applies. (Avoids silently dropping inits from the pairing.)
            let nc_fixture = fixture
                .replace("_preprocessed_layout_gkr.json", "_layout_no_caches_gkr.json")
                .replace("_layout_gkr.json", "_layout_no_caches_gkr.json");
            let Some((clayer, _)) = crate::try_load_l0(fixture) else {
                continue;
            };
            let Some((nlayer, _)) = crate::try_load_l0(&nc_fixture) else {
                println!("[EXPRDIFF] {name:<32} no-cache fixture MISSING");
                continue;
            };
            let c = analyze(&clayer);
            let n = analyze(&nlayer);
            println!(
                "[EXPRDIFF] {name:<30}\n  cache:    exprs={:<5} reads={:<5} priors={:<5} roots[inner={} cache={} constr={}] cache-root fanOUT(max={} hist={:?}) consumer fanIN(max={} hist={:?})\n  no-cache: exprs={:<5} reads={:<5} priors={:<5} roots[inner={} cache={} constr={}]",
                c.exprs, c.reads, c.priors, c.inner, c.cache, c.constraint, c.max_fanout, c.fanout_hist, c.max_fanin, c.fanin_hist,
                n.exprs, n.reads, n.priors, n.inner, n.cache, n.constraint
            );
        }
    }

    /// REPORT: full-circuit fan-out of EVERY materialized value, all sink kinds, counting
    /// both in-layer reuse (`Source(Prior)`) and cross-layer reload points
    /// (`Source(Read{LayerOutput|CacheOutput})` in a later layer). Each such source is one
    /// reload point (the value is read once then shared internally via ExprId). If fan-out
    /// is ≤ 1 universally, reload is never beneficial (a single use comes from the
    /// accumulator within a layer / merged graph; across unmerged layers it is exactly one
    /// unavoidable boundary read). Confirms whether the fan-out-1 property holds for ALL
    /// outputs (incl. one layer's output read by the next), not just in-layer Cache.
    #[test]
    #[ignore = "report: full-circuit fan-out of all materialized outputs (in-layer + cross-layer)"]
    fn all_outputs_fanout_full_circuit() {
        use cs::gkr_compiler::dag_ir::{Expr, ExprId, ReadPlace, SinkInfo, SinkKind, SourceKind};
        use std::collections::BTreeMap;

        fn tag_name(t: u8) -> &'static str {
            match t {
                0 => "Inner",
                1 => "Cache",
                2 => "Export",
                3 => "Scratch",
                _ => "?",
            }
        }

        for &fixture in ALL_22_L0_FIXTURES {
            let name = fixture
                .trim_end_matches("_layout_gkr.json")
                .trim_end_matches("_layout_no_caches_gkr.json");
            let flavor = if fixture.contains("no_caches") {
                "no-cache"
            } else {
                "cache"
            };
            let (dag, _a, _c) = crate::load_layer_source(fixture);

            // key = (tag, layer, offset); producers start at fan-out 0
            let mut fanout: BTreeMap<(u8, i64, i64), usize> = BTreeMap::new();
            // per-layer: producer ExprId -> producer key (for in-layer shared-ExprId reuse
            // attribution — Part B replaces the old RootId-keyed `Prior` attribution).
            let mut expr_key: Vec<BTreeMap<u32, (u8, i64, i64)>> = Vec::new();
            for layer in &dag.layers {
                let mut m = BTreeMap::new();
                for root in layer.roots.iter() {
                    if let Some(SinkInfo { kind, .. }) = &root.materialize {
                        let key = match *kind {
                            SinkKind::Inner { layer, offset } => (0u8, layer as i64, offset as i64),
                            SinkKind::Cache { layer, offset } => (1u8, layer as i64, offset as i64),
                            SinkKind::Export { slot } => (2u8, -1, slot as i64),
                            SinkKind::Scratch { slot } => (3u8, -1, slot as i64),
                        };
                        fanout.entry(key).or_insert(0);
                        m.insert(root.expr.0, key);
                    }
                }
                expr_key.push(m);
            }
            for (lj, layer) in dag.layers.iter().enumerate() {
                // Cross-layer reload points: a later layer's Read of a producer place.
                for s in &layer.sources {
                    if let SourceKind::Read { place } = &s.kind {
                        let key = match place {
                            ReadPlace::LayerOutput { layer, offset } => {
                                Some((0u8, *layer as i64, *offset as i64))
                            }
                            ReadPlace::CacheOutput { layer, offset } => {
                                Some((1u8, *layer as i64, *offset as i64))
                            }
                            ReadPlace::Scratch { slot } => Some((3u8, -1, *slot as i64)),
                            _ => None,
                        };
                        if let Some(k) = key {
                            *fanout.entry(k).or_insert(0) += 1;
                        }
                    }
                }
                // In-layer reuse: a root cone that reaches ANOTHER root's producer `expr`
                // is one shared-ExprId reuse of that producer (the old `Source(Prior)` edge).
                for root in layer.roots.iter() {
                    let mut visited: std::collections::BTreeSet<u32> =
                        std::collections::BTreeSet::new();
                    let mut stack: Vec<ExprId> = vec![root.expr];
                    let mut first = true;
                    while let Some(eid) = stack.pop() {
                        if !visited.insert(eid.0) {
                            continue;
                        }
                        if !first {
                            if let Some(k) = expr_key[lj].get(&eid.0) {
                                *fanout.entry(*k).or_insert(0) += 1;
                            }
                        }
                        first = false;
                        match &layer.exprs[eid.0 as usize] {
                            Expr::Source(sid) => {
                                if let SourceKind::LookupValue { query, .. } =
                                    &layer.sources[sid.0 as usize].kind
                                {
                                    stack.push(*query);
                                }
                            }
                            Expr::Add(ch) | Expr::Mul(ch) => stack.extend(ch.iter().copied()),
                        }
                    }
                }
            }

            let mut by_tag: BTreeMap<u8, (usize, usize, BTreeMap<usize, usize>)> = BTreeMap::new();
            for ((tag, _, _), fo) in &fanout {
                let e = by_tag.entry(*tag).or_insert((0, 0, BTreeMap::new()));
                e.0 += 1; // producer count
                e.1 = e.1.max(*fo); // max fan-out
                *e.2.entry(*fo).or_insert(0) += 1;
            }
            let layers = dag.layers.len();
            let parts: Vec<String> = by_tag
                .iter()
                .map(|(tag, (n, max, hist))| {
                    format!("{}[n={n} max={max} hist={hist:?}]", tag_name(*tag))
                })
                .collect();
            println!(
                "[FANOUT] {name:<32} {flavor:<8} layers={layers:<3} {}",
                parts.join(" ")
            );
        }
    }

    /// REPORT: the reuse the caching machinery ACTUALLY serves, now that materialized
    /// reload is out. Counts `ExprId` fan-out within the expr DAG (distinct parent exprs +
    /// root refs). `Add`/`Mul` nodes with fan-out > 1 are shared INTERMEDIATE
    /// sub-expressions — computed once, reused → keep-resident-or-recompute (no reload;
    /// they have no committed copy). `extra_uses = Σ(fanout-1)` is the cache-hit
    /// opportunity (reuse events caching saves vs recomputing). Base-leaf (`Read`) reuse is
    /// reported alongside (keep-vs-reread; can't recompute). Sizes the remaining problem.
    #[test]
    #[ignore = "report: intermediate sub-expression reuse (caching pressure after reload removed)"]
    fn intermediate_expr_reuse() {
        use cs::gkr_compiler::dag_ir::{Expr, Root, SourceKind};
        use std::collections::BTreeSet;

        for &fixture in ALL_22_L0_FIXTURES {
            let name = fixture
                .trim_end_matches("_layout_gkr.json")
                .trim_end_matches("_layout_no_caches_gkr.json");
            let flavor = if fixture.contains("no_caches") {
                "no-cache"
            } else {
                "cache"
            };
            let Some((layer, _)) = crate::try_load_l0(fixture) else {
                continue;
            };
            let mut refcount = vec![0usize; layer.exprs.len()];
            for e in &layer.exprs {
                if let Expr::Add(ch) | Expr::Mul(ch) = e {
                    let uniq: BTreeSet<u32> = ch.iter().map(|c| c.0).collect();
                    for c in uniq {
                        refcount[c as usize] += 1;
                    }
                }
            }
            for root in &layer.roots {
                let eid = root.expr;
                refcount[eid.0 as usize] += 1;
            }
            let (mut it_total, mut it_reused, mut it_max, mut it_extra) = (0usize, 0, 0, 0usize);
            let (mut lf_total, mut lf_reused, mut lf_max, mut lf_extra) = (0usize, 0, 0, 0usize);
            for (eid, e) in layer.exprs.iter().enumerate() {
                let rc = refcount[eid];
                match e {
                    Expr::Add(_) | Expr::Mul(_) => {
                        it_total += 1;
                        it_max = it_max.max(rc);
                        if rc > 1 {
                            it_reused += 1;
                            it_extra += rc - 1;
                        }
                    }
                    Expr::Source(sid) => {
                        if matches!(layer.sources[sid.0 as usize].kind, SourceKind::Read { .. }) {
                            lf_total += 1;
                            lf_max = lf_max.max(rc);
                            if rc > 1 {
                                lf_reused += 1;
                                lf_extra += rc - 1;
                            }
                        }
                    }
                }
            }
            println!(
                "[REUSE] {name:<30} {flavor:<8} intermediate(Add/Mul): total={it_total:<5} reused={it_reused:<5} max={it_max:<3} extra_uses={it_extra:<5} | leaf(Read): total={lf_total:<4} reused={lf_reused:<4} max={lf_max:<4} extra_uses={lf_extra}"
            );
        }
    }

    /// REPORT: the TRUE use-count of materialized values. Because `intern_source`
    /// deduplicates `SourceKind` (arena.rs), a value referenced by K consumers shares ONE
    /// interned `Prior`/cross-layer-`Read` source — so "fan-out via source count" is ~1 by
    /// construction (an interning artifact), NOT a use count. This measures the real reuse:
    /// the ExprId refcount (distinct parent exprs + roots) of each interned materialized-value
    /// source. max_uses > 1 means the value IS reused (read once, shared) → reload/keep
    /// decisions remain live; the earlier "used at most once" framing was an artifact.
    #[test]
    #[ignore = "report: true use-count of materialized values (refutes/quantifies the fan-out-1 artifact)"]
    fn materialized_source_use_count() {
        use cs::gkr_compiler::dag_ir::{Expr, ReadPlace, SourceKind};
        use std::collections::BTreeSet;
        for &fixture in ALL_22_L0_FIXTURES {
            let name = fixture
                .trim_end_matches("_layout_gkr.json")
                .trim_end_matches("_layout_no_caches_gkr.json");
            let flavor = if fixture.contains("no_caches") { "no-cache" } else { "cache" };
            let Some((layer, _)) = crate::try_load_l0(fixture) else { continue };
            let mut refcount = vec![0usize; layer.exprs.len()];
            for e in &layer.exprs {
                if let Expr::Add(ch) | Expr::Mul(ch) = e {
                    for c in ch.iter().map(|c| c.0).collect::<BTreeSet<_>>() {
                        refcount[c as usize] += 1;
                    }
                }
            }
            for root in &layer.roots {
                let eid = root.expr;
                refcount[eid.0 as usize] += 1;
            }
            // Part B: in-layer reuse of a materialized value is the ExprId refcount of the
            // CACHE ROOT's shared `expr` (the old `Source(Prior)` is gone). Cross-layer
            // reload points are still cross-layer `Read{Layer/CacheOutput}` sources.
            let cache_roots = cache_expr_to_root(&layer);
            let (mut p_n, mut p_reused, mut p_max) = (0usize, 0usize, 0usize);
            let (mut x_n, mut x_reused, mut x_max) = (0usize, 0usize, 0usize);
            for (&expr, _) in cache_roots.iter() {
                let rc = refcount[expr.0 as usize];
                p_n += 1;
                p_max = p_max.max(rc);
                if rc > 1 { p_reused += 1; }
            }
            for (eid, e) in layer.exprs.iter().enumerate() {
                if let Expr::Source(sid) = e {
                    let rc = refcount[eid];
                    if let SourceKind::Read { place } = &layer.sources[sid.0 as usize].kind {
                        if matches!(place, ReadPlace::LayerOutput { .. } | ReadPlace::CacheOutput { .. }) {
                            x_n += 1;
                            x_max = x_max.max(rc);
                            if rc > 1 { x_reused += 1; }
                        }
                    }
                }
            }
            println!(
                "[USECOUNT] {name:<30} {flavor:<8} in-layer cache-reuse: n={p_n:<4} reused(>1)={p_reused:<4} max_uses={p_max:<3} | cross-layer Read(Layer/CacheOutput): n={x_n:<4} reused={x_reused:<4} max_uses={x_max}"
            );
        }
    }

    /// REPORT: for each value materialized as a `Cache` root in the cache layout, find the
    /// SAME expression in the no-cache layout (structural fingerprint over base sources) and
    /// report ITS use-count there. Answers: is the materialized value reused ≤ 2× in no-cache
    /// too (just not committed), or does the cache layout's `Prior` fan-out (≤ 2) understate a
    /// higher true reuse that surfaces as CSE sharing in no-cache? Fingerprint = structural
    /// hash (op + sorted child fingerprints; `Source` keyed by `SourceKind` debug, which is
    /// cross-layout-stable for `Read`/`Constant`). Assumes child ExprId < parent (interned).
    ///
    /// LIMITATION (verified by review, wf_ba11900c): the `unmatched` count is NOT a structural
    /// signal. `LookupValue{query: ExprId}` and `Prior{id: RootId}` Debug-print LAYOUT-SPECIFIC
    /// arena/root indices, so a cache root whose cone holds a lookup/memory fold or a
    /// cache-of-cache fingerprints differently across layouts even when structurally identical.
    /// Cache roots are dominated by exactly those, so most show as `unmatched` SPURIOUSLY — the
    /// values DO exist in no_cache (same lowering helpers), the matcher just can't see them.
    /// Only the `matched` subset (pure Add/Mul over Read/Constant) is meaningful; it confirms
    /// use-count ≤ 2. A sound matcher would recurse into `query` and resolve `Prior` to the
    /// referenced root's fingerprint.
    #[test]
    #[ignore = "report: cross-layout use-count of cache-materialized values (matched subset only — see LIMITATION)"]
    fn cache_root_use_count_in_no_cache() {
        use cs::gkr_compiler::dag_ir::{DagLayer, Expr, SinkInfo, SinkKind};
        use std::collections::{BTreeMap, BTreeSet, HashMap};
        use std::hash::{Hash, Hasher};

        fn fingerprints(layer: &DagLayer) -> Vec<u64> {
            let mut fp = vec![0u64; layer.exprs.len()];
            for (i, e) in layer.exprs.iter().enumerate() {
                let mut h = std::collections::hash_map::DefaultHasher::new();
                match e {
                    Expr::Source(sid) => {
                        0u8.hash(&mut h);
                        format!("{:?}", layer.sources[sid.0 as usize].kind).hash(&mut h);
                    }
                    Expr::Add(ch) | Expr::Mul(ch) => {
                        (if matches!(e, Expr::Add(_)) { 1u8 } else { 2u8 }).hash(&mut h);
                        let mut cs: Vec<u64> = ch.iter().map(|c| fp[c.0 as usize]).collect();
                        cs.sort_unstable();
                        cs.hash(&mut h);
                    }
                }
                fp[i] = h.finish();
            }
            fp
        }
        fn use_counts(layer: &DagLayer) -> Vec<usize> {
            let mut rc = vec![0usize; layer.exprs.len()];
            for e in &layer.exprs {
                if let Expr::Add(ch) | Expr::Mul(ch) = e {
                    for c in ch.iter().map(|c| c.0).collect::<BTreeSet<u32>>() {
                        rc[c as usize] += 1;
                    }
                }
            }
            for root in &layer.roots {
                let eid = root.expr;
                rc[eid.0 as usize] += 1;
            }
            rc
        }

        for &fixture in ALL_22_L0_FIXTURES {
            if fixture.contains("no_caches") {
                continue;
            }
            let name = fixture.trim_end_matches("_layout_gkr.json");
            let nc_fixture = fixture
                .replace("_preprocessed_layout_gkr.json", "_layout_no_caches_gkr.json")
                .replace("_layout_gkr.json", "_layout_no_caches_gkr.json");
            let Some((clayer, _)) = crate::try_load_l0(fixture) else { continue };
            let Some((nlayer, _)) = crate::try_load_l0(&nc_fixture) else {
                println!("[XLAYER] {name:<30} no-cache MISSING");
                continue;
            };
            let cfp = fingerprints(&clayer);
            let nfp = fingerprints(&nlayer);
            let nrc = use_counts(&nlayer);
            let mut nmap: HashMap<u64, usize> = HashMap::new();
            for (i, &f) in nfp.iter().enumerate() {
                let e = nmap.entry(f).or_insert(0);
                *e = (*e).max(nrc[i]);
            }
            let (mut cache_roots, mut matched, mut unmatched, mut nc_max) = (0usize, 0, 0, 0usize);
            let mut nc_hist: BTreeMap<usize, usize> = BTreeMap::new();
            for root in &clayer.roots {
                // Cache root: a `Cache` materialize with no claim.
                let is_cache = matches!(
                    &root.materialize,
                    Some(SinkInfo { kind: SinkKind::Cache { .. }, .. })
                ) && root.claim.is_none();
                if is_cache {
                    let expr = root.expr;
                    cache_roots += 1;
                    match nmap.get(&cfp[expr.0 as usize]) {
                        Some(&uc) => {
                            matched += 1;
                            *nc_hist.entry(uc).or_default() += 1;
                            nc_max = nc_max.max(uc);
                        }
                        None => unmatched += 1,
                    }
                }
            }
            println!(
                "[XLAYER] {name:<30} cache_roots={cache_roots:<4} matched_in_nocache={matched:<4} unmatched={unmatched:<4} | no_cache use-count of matched: max={nc_max} hist={nc_hist:?}"
            );
        }
    }

    /// REPORT: for each cache root with exactly 2 consumers, how far apart are its two use
    /// sites in root-emission order? Answers "are the 2 uses emitted one after another"
    /// (local → held briefly, free to co-locate) vs spread (needs cross-root residency). A
    /// consumer of cache root V = a root whose expr cone contains `Source(Prior{id=V})`.
    /// Reports the consumer-pair gap |c2-c1| and the gap from V's own emission index.
    #[test]
    #[ignore = "report: emission-order adjacency of the 2 use sites of use-count-2 cache values"]
    fn cache_root_consumer_adjacency() {
        use std::collections::BTreeMap;

        for &fixture in ALL_22_L0_FIXTURES {
            if fixture.contains("no_caches") {
                continue;
            }
            let name = fixture.trim_end_matches("_layout_gkr.json");
            let Some((layer, _)) = crate::try_load_l0(fixture) else { continue };
            // cache root `expr` -> its own RootId; and cache RootId -> its own root index.
            let cache_roots = cache_expr_to_root(&layer);
            let mut cache_idx: BTreeMap<u32, usize> = BTreeMap::new();
            for (&_expr, &rid) in cache_roots.iter() {
                cache_idx.insert(rid.0, rid.0 as usize);
            }
            // cache RootId -> consumer root indices (Part B: roots whose cone reaches the
            // cache root's shared `expr` — the old `Source(Prior{id})` consumer).
            let mut consumers: BTreeMap<u32, Vec<usize>> = BTreeMap::new();
            for (ri, root) in layer.roots.iter().enumerate() {
                for cache_rid in cache_roots_in_cone(&layer, root.expr, &cache_roots) {
                    // A cache root trivially reaches its own expr — that is not consumption.
                    if cache_rid.0 as usize != ri {
                        consumers.entry(cache_rid.0).or_default().push(ri);
                    }
                }
            }
            let (mut n2, mut adj, mut pair_gap_max, mut prod_gap_max) = (0usize, 0usize, 0usize, 0usize);
            let mut pair_gap_hist: BTreeMap<usize, usize> = BTreeMap::new();
            for (cid, cons) in &consumers {
                if cons.len() != 2 {
                    continue;
                }
                n2 += 1;
                let gap = cons[1] - cons[0];
                pair_gap_hist.entry(gap).or_default();
                *pair_gap_hist.get_mut(&gap).unwrap() += 1;
                pair_gap_max = pair_gap_max.max(gap);
                if gap == 1 {
                    adj += 1;
                }
                let prod = cache_idx[cid];
                prod_gap_max = prod_gap_max.max(cons[0].saturating_sub(prod).max(cons[1].saturating_sub(prod)));
            }
            let bucket = |g: usize| if g == 1 { "1" } else if g <= 4 { "2-4" } else if g <= 16 { "5-16" } else { ">16" };
            let mut buckets: BTreeMap<&str, usize> = BTreeMap::new();
            for (g, c) in &pair_gap_hist {
                *buckets.entry(bucket(*g)).or_default() += c;
            }
            println!(
                "[ADJ] {name:<30} usecount2={n2:<4} adjacent(gap=1)={adj:<4} pair_gap_max={pair_gap_max:<4} prod_to_use_gap_max={prod_gap_max:<4} | gap buckets={buckets:?}"
            );
        }
    }

    /// INVARIANT: every `Cache` root belongs to a SINGLE relation — all of its in-layer
    /// consumers (Part B: roots whose cone reaches the cache root's shared `expr`, the old
    /// `Source(Prior{id})` consumer) share one FULL relation identity `(RootGroup,
    /// relation_index)`. This is what makes the relation a sound atomic scheduling unit (the
    /// fold is privately owned by one relation). Measured true today (diff_relation==0 on all
    /// 11 circuits); ASSERTED here so that if a future generator ever CSE-merges a fold across
    /// relations the build fails LOUDLY (then build the cross-relation handling — YAGNI until
    /// then, per RR). Cache roots with no in-layer consumer (cross-layer only) are vacuously OK.
    ///
    /// Identity is the FULL `(group, relation_index)` — NOT `relation_index` alone, which
    /// conflated `Gates[0]` with `GatesExternal[0]` (matches `relation_units` in instance.rs
    /// and the validator key in validate.rs).
    #[test]
    #[ignore = "research invariant: every Cache root belongs to a single relation"]
    fn dual_use_cache_consumers_share_relation() {
        use cs::gkr_compiler::dag_ir::RootGroup;
        use std::collections::{BTreeMap, HashSet};

        for &fixture in ALL_22_L0_FIXTURES {
            if fixture.contains("no_caches") {
                continue;
            }
            let name = fixture.trim_end_matches("_layout_gkr.json");
            let Some((layer, _)) = crate::try_load_l0(fixture) else { continue };
            let cache_roots = cache_expr_to_root(&layer);
            // cache RootId -> consumer root indices (cone reaches the cache root's `expr`).
            let mut consumers: BTreeMap<u32, Vec<usize>> = BTreeMap::new();
            for (ri, root) in layer.roots.iter().enumerate() {
                for cache_rid in cache_roots_in_cone(&layer, root.expr, &cache_roots) {
                    if cache_rid.0 as usize != ri {
                        consumers.entry(cache_rid.0).or_default().push(ri);
                    }
                }
            }
            let (mut checked, mut dual) = (0usize, 0usize);
            for (cid, cons) in &consumers {
                // distinct FULL relation identity (group, relation_index) among consumers.
                let rels: HashSet<(RootGroup, usize)> = cons
                    .iter()
                    .filter_map(|&r| {
                        layer.roots[r]
                            .claim
                            .as_ref()
                            .map(|c| (c.origin.group.clone(), c.origin.relation_index))
                    })
                    .collect();
                assert!(
                    rels.len() <= 1,
                    "{name}: cache root {cid} is consumed by {} relations {:?} — violates \
                     single-relation ownership; the relation-as-unit model assumes a fold belongs \
                     to one relation. Build the cross-relation handling now.",
                    rels.len(),
                    rels
                );
                checked += 1;
                if cons.len() == 2 {
                    dual += 1;
                }
            }
            println!(
                "[DUAL] {name:<30} cache_roots={:<4} with_consumers={checked:<4} dual_use={dual:<4} (all belong to <=1 relation)",
                cache_roots.len()
            );
        }
    }

    fn duplicate_traffic_reads(trace: &CacheTrace) -> Vec<(u32, usize)> {
        use std::collections::BTreeMap;

        let mut counts = BTreeMap::new();
        for event in &trace.events {
            if let CacheTraceEvent::TrafficRead { value, .. } = *event {
                *counts.entry(value).or_insert(0usize) += 1;
            }
        }
        counts.into_iter().filter(|&(_, count)| count > 1).collect()
    }

    fn duplicate_read_site_details(
        trace: &CacheTrace,
        sites: &[DemandSite],
        genome: &Genome,
        inst: &OracleInstance,
    ) -> Vec<(
        u32,
        Vec<(usize, u32, u32, u32, u32, Option<usize>)>,
        Vec<(u32, Option<usize>)>,
        Vec<String>,
    )> {
        let duplicates = duplicate_traffic_reads(trace);
        let order = decode_root_occurrence_order(inst, genome);
        let classes = classify_values(inst);
        let replay = Replay::new(inst, sites, genome, classes, &order, false);
        duplicates
            .into_iter()
            .map(|(value, _)| {
                let value_sites = sites
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, site)| {
                        (site.value == value).then_some((
                            idx,
                            site.root,
                            inst.roots[site.root as usize],
                            site.consumer,
                            site.input_index,
                            occurrence_position(&order, site.root as usize),
                        ))
                    })
                    .collect();
                let read_events = trace
                    .events
                    .iter()
                    .filter_map(|event| match *event {
                        CacheTraceEvent::TrafficRead {
                            root,
                            value: event_value,
                            site_idx,
                        } if event_value == value => Some((root, site_idx)),
                        _ => None,
                    })
                    .collect();
                let cache_events: Vec<String> = trace
                    .events
                    .iter()
                    .filter_map(|event| match *event {
                        CacheTraceEvent::Admit { site_idx, value: event_value }
                            if event_value == value =>
                        {
                            let site = sites.get(site_idx);
                            let root_position =
                                site.and_then(|site| occurrence_position(&order, site.root as usize));
                            Some(format!(
                                "admit site={site_idx} root_position={root_position:?} site={site:?}",
                            ))
                        }
                        CacheTraceEvent::NoFutureDemand {
                            site_idx,
                            value: event_value,
                        } if event_value == value => {
                            let site = sites.get(site_idx);
                            let root_position =
                                site.and_then(|site| occurrence_position(&order, site.root as usize));
                            Some(format!(
                                "no_future site={site_idx} root_position={root_position:?} site={site:?}",
                            ))
                        }
                        CacheTraceEvent::PressureReject {
                            site_idx,
                            value: event_value,
                        } if event_value == value => {
                            let site = sites.get(site_idx);
                            let root_position =
                                site.and_then(|site| occurrence_position(&order, site.root as usize));
                            Some(format!(
                                "pressure_reject site={site_idx} root_position={root_position:?} site={site:?}",
                            ))
                        }
                        CacheTraceEvent::PressureAdmit {
                            site_idx,
                            value: event_value,
                        } if event_value == value => {
                            let site = sites.get(site_idx);
                            let root_position =
                                site.and_then(|site| occurrence_position(&order, site.root as usize));
                            Some(format!(
                                "pressure_admit site={site_idx} root_position={root_position:?} site={site:?}",
                            ))
                        }
                        CacheTraceEvent::Evict {
                            site_idx,
                            victim,
                            victim_last_site,
                            victim_remaining,
                            cause,
                        } if victim == value => {
                            let site = site_idx.and_then(|idx| sites.get(idx));
                            let root_position =
                                site.and_then(|site| occurrence_position(&order, site.root as usize));
                            Some(format!(
                                "site={site_idx:?} root_position={root_position:?} site={site:?} last_site={victim_last_site:?} victim_remaining={victim_remaining} cause={cause:?}",
                            ))
                        }
                        _ => None,
                    })
                    .collect();
                let mut cache_events = cache_events;
                cache_events.insert(
                    0,
                    format!("initial_remaining={}", replay.remaining_demands[value as usize]),
                );
                (value, value_sites, read_events, cache_events)
            })
            .collect()
    }

    fn occurrence_position(order: &[usize], root_occurrence: usize) -> Option<usize> {
        order
            .iter()
            .enumerate()
            .find_map(|(idx, &candidate)| (candidate == root_occurrence).then_some(idx))
    }

    #[test]
    #[ignore = "research invariant: optimizer scores must not go below unique physical read floor"]
    fn real_all_22_l0_scores_never_below_read_place_floor() {
        use crate::s3_gap::instance::extract_instance;

        const POPULATION: usize = 1000;
        const EVAL_BUDGET: usize = 10_000;
        const FINAL_STARTS: usize = 16;
        const FINAL_EVAL_BUDGET: usize = 2_000;

        let mut checked = 0usize;
        for &fixture in ALL_22_L0_FIXTURES {
            let name = fixture
                .trim_end_matches("_layout_gkr.json")
                .trim_end_matches("_layout_no_caches_gkr.json");
            let flavor = if fixture.contains("no_caches") {
                "no-cache"
            } else {
                "cache"
            };
            let label = format!("{name}/{flavor}");
            let Some((layer, cross)) = crate::try_load_l0(fixture) else {
                println!("[READ-FLOOR] {label:<52} LOAD_FAILED");
                continue;
            };
            let floor = reachable_read_stats(&layer, &cross).read_place_cells as u64;
            let inst = extract_instance(&layer, &cross, crate::REAL_BUDGET);
            let sites = enumerate_demand_sites(&inst);
            if inst.roots.is_empty() || sites.is_empty() {
                println!(
                    "[READ-FLOOR] {label:<52} floor={floor:<4} nodes={:<5} roots={:<4} sites={:<4} SKIP",
                    inst.nodes.len(),
                    inst.roots.len(),
                    sites.len(),
                );
                continue;
            }

            let smoke = compact_smoke(
                &inst,
                &sites,
                POPULATION,
                EVAL_BUDGET,
                FINAL_STARTS,
                FINAL_EVAL_BUDGET,
            );
            let baseline = smoke.baseline.traffic;
            let optimized = smoke.optimized.best_score.traffic;
            let final_best = smoke.final_states.best.traffic;
            println!(
                "[READ-FLOOR] {label:<52} floor={floor:<4} baseline={baseline:<4} opt={optimized:<4} final={final_best:<4}"
            );
            assert!(
                baseline >= floor,
                "{label}: baseline traffic {baseline} is below read-place floor {floor}"
            );
            assert!(
                optimized >= floor,
                "{label}: optimized traffic {optimized} is below read-place floor {floor}"
            );
            assert!(
                final_best >= floor,
                "{label}: final best traffic {final_best} is below read-place floor {floor}"
            );
            checked += 1;
        }

        assert_eq!(checked, ALL_22_L0_FIXTURES.len());
    }

    #[test]
    #[ignore = "research verdict: optimizer vs neutral baseline at REAL_BUDGET across the corpus"]
    fn real_all_22_l0_optimized_vs_neutral_baseline() {
        use crate::s3_gap::instance::extract_instance;

        // M6: the motivating OPEN question — does joint order+caching beat the baseline
        // at REAL_BUDGET? The optimizer SEEDS include the neutral genome, so it can never
        // do WORSE (asserted per fixture). We REPORT the per-fixture gap (baseline -
        // optimized); fixtures with a positive gap are evidence order/caching helps, and
        // a no-gap-everywhere result IS the (negative) verdict — recorded, not hidden.
        //
        // M7: the baseline is `Genome::neutral` (identity order, zero biases), NOT the
        // production residency scheduler. Beating neutral is NECESSARY but NOT SUFFICIENT
        // evidence of production payoff; when the production order+residency for these
        // layers is extractable it must replace neutral as the baseline.
        //
        // Budget reflects the OFFLINE-AMORTIZED search regime: the optimal schedule is
        // computed ONCE per (circuit, layout, layer, budget) and baked into the compiled
        // artifact, so the search can run long. SA's uphill escape is budget-gated — its
        // value materializes at this scale (16k: total_gap 422 vs 404 at the old 2k quick
        // budget; SA isolated +11). See ad02f476.
        const POPULATION: usize = 200;
        const EVAL_BUDGET: usize = 16_000;
        const FINAL_STARTS: usize = 4;
        const FINAL_EVAL_BUDGET: usize = 2_000;

        let mut checked = 0usize;
        let mut improved = 0usize;
        let mut no_gap = 0usize;
        let mut total_gap = 0i64;
        for &fixture in ALL_22_L0_FIXTURES {
            let name = fixture
                .trim_end_matches("_layout_gkr.json")
                .trim_end_matches("_layout_no_caches_gkr.json");
            let Some((layer, cross)) = crate::try_load_l0(fixture) else {
                println!("[M6] {name:<48} LOAD_FAILED");
                continue;
            };
            let inst = extract_instance(&layer, &cross, crate::REAL_BUDGET);
            let sites = enumerate_demand_sites(&inst);
            if inst.roots.is_empty() || sites.is_empty() {
                continue;
            }
            let smoke = compact_smoke(
                &inst,
                &sites,
                POPULATION,
                EVAL_BUDGET,
                FINAL_STARTS,
                FINAL_EVAL_BUDGET,
            );
            let base = smoke.baseline.traffic;
            let opt = smoke
                .optimized
                .best_score
                .traffic
                .min(smoke.final_states.best.traffic);
            // Optimizer considers the neutral seed, so it must never regress below it.
            assert!(
                opt <= base,
                "{name}: optimizer traffic {opt} worse than neutral baseline {base}"
            );
            let gap = base as i64 - opt as i64;
            total_gap += gap;
            if gap > 0 {
                improved += 1;
            } else {
                no_gap += 1;
            }
            println!("[M6] {name:<48} baseline={base:<5} optimized={opt:<5} gap={gap}");
            checked += 1;
        }
        assert!(checked > 0, "no fixtures checked — corpus setup broken");
        println!(
            "[M6][VERDICT] improved={improved}/{checked} (no-gap={no_gap}), total_gap={total_gap}. \
             Baseline=neutral genome — necessary but NOT sufficient vs the production scheduler."
        );
    }

    #[test]
    #[ignore = "research A/B: unit-keyed group-atomic search vs flat order across the corpus"]
    fn real_all_22_l0_group_atomic_vs_flat() {
        use crate::s3_gap::instance::{extract_instance, relation_units};

        // STAGE 1.5 of the relation-unit prototype (optimizer-only, ZERO IR change):
        // does scheduling each gate relation as ONE indivisible unit reduce read traffic
        // vs the unconstrained flat order? The unit is (RootGroup, relation_index) from
        // layer.origins (cache / materialization-only roots, which have no origin, are
        // singletons). The grouped arm's genome is UNIT-KEYED — one ordering key per
        // unit — so a swap/insert/reverse relocates a whole unit and members never
        // separate (the unit is the scheduling atom; there is nothing to "keep
        // together"). The flat arm is the historical per-occurrence search.
        //
        // SEED PARITY: the grouped arm is seeded from the SAME population as the flat
        // arm, projected into unit-keys (`project_genome_to_units`) — identical cache
        // biases, unit order = the flat order's per-unit minimum. So the two arms start
        // from the same places and ONLY the move space differs (occurrence vs unit),
        // isolating the search-dynamics effect from seed quality.
        const POPULATION: usize = 200;
        const EVAL_BUDGET: usize = 16_000;

        let mut checked = 0usize;
        let mut grouped_better = 0usize;
        let mut flat_better = 0usize;
        let mut equal = 0usize;
        let mut total_flat = 0i64;
        let mut total_grouped = 0i64;
        let mut flat_nonatomic = 0usize;
        for &fixture in ALL_22_L0_FIXTURES {
            let name = fixture
                .trim_end_matches("_layout_gkr.json")
                .trim_end_matches("_layout_no_caches_gkr.json");
            let flavor = if fixture.contains("no_caches") {
                "no-cache"
            } else {
                "cache"
            };
            let label = format!("{name}/{flavor}");
            let Some((layer, cross)) = crate::try_load_l0(fixture) else {
                println!("[GROUP-AB] {label:<52} LOAD_FAILED");
                continue;
            };
            let inst = extract_instance(&layer, &cross, crate::REAL_BUDGET);
            let sites = enumerate_demand_sites(&inst);
            if inst.roots.is_empty() || sites.is_empty() {
                continue;
            }
            let unit_of = relation_units(&layer);
            assert_eq!(
                unit_of.len(),
                inst.roots.len(),
                "{label}: relation_units must align with the Output-root occurrences"
            );
            let units = unit_members(&unit_of);
            // How much does grouping actually constrain? distinct units and how many
            // bind >1 root (the num/den-pair relations whose fold we co-locate).
            let n_units = units.len();
            let multi = units.iter().filter(|m| m.len() > 1).count();

            let flat_pop = smoke_genome_population(&inst, &sites, POPULATION);
            let unit_pop: Vec<Genome> = flat_pop
                .iter()
                .map(|g| project_genome_to_units(g, &units))
                .collect();
            let flat = optimize_from_population(&inst, &sites, flat_pop, EVAL_BUDGET);
            let grouped =
                optimize_from_population_grouped(&inst, &sites, unit_pop, EVAL_BUDGET, &units);

            // DIAGNOSIS: is flat's winning order reachable under atomicity? If flat's best
            // order keeps every unit contiguous, the grouped arm's space CONTAINS it, so a
            // grouped regression is a search/seed artifact. If flat's best SPLITS a unit,
            // atomicity structurally forbids it ⇒ the regression is a genuine trade-off.
            let f_order = decode_root_occurrence_order(&inst, &flat.best_genome);
            let f_contig = order_keeps_units_contiguous(&f_order, &units);
            if !f_contig {
                flat_nonatomic += 1;
            }

            // The grouped best must keep every unit contiguous (atomicity by construction).
            let g_order = decode_grouped_occurrence_order(&inst, &grouped.best_genome, &units);
            for m in &units {
                let pos: Vec<usize> = m
                    .iter()
                    .map(|&occ| g_order.iter().position(|&o| o == occ).unwrap())
                    .collect();
                let (lo, hi) = (
                    *pos.iter().min().unwrap(),
                    *pos.iter().max().unwrap(),
                );
                assert_eq!(hi - lo + 1, m.len(), "{label}: grouped best split a unit");
            }

            let f = flat.best_score.traffic;
            let g = grouped.best_score.traffic;
            let ff = flat.best_score.feasible;
            let gf = grouped.best_score.feasible;
            let delta = f as i64 - g as i64; // > 0 ⇒ group-atomic wins
            total_flat += f as i64;
            total_grouped += g as i64;
            match delta.cmp(&0) {
                std::cmp::Ordering::Greater => grouped_better += 1,
                std::cmp::Ordering::Less => flat_better += 1,
                std::cmp::Ordering::Equal => equal += 1,
            }
            println!(
                "[GROUP-AB] {label:<52} roots={:<4} units={n_units:<4} multi={multi:<4} \
                 flat={f:<5}{} grouped={g:<5}{} delta={delta:<4} flat_atomic={}",
                inst.roots.len(),
                if ff { " " } else { "!" },
                if gf { " " } else { "!" },
                if f_contig { "yes" } else { "NO" },
            );
            checked += 1;
        }
        assert!(checked > 0, "no fixtures checked — corpus setup broken");
        // KEY DIAGNOSIS: flat_nonatomic = how many fixtures' UNCONSTRAINED (flat) best
        // order splits a unit. Measured 1/22 (add_sub/cache) — and even there the
        // grouped arm's ATOMIC best beats flat's non-atomic one (44 < 45). So
        // relation-atomicity costs ~nothing at the optimum: 21/22 flat optima are
        // already unit-contiguous, and the lone exception has a better atomic order.
        // With seed parity (grouped seeded from the projected flat population) the
        // earlier regressions collapse to one (mem_subword/cache, flat_atomic=yes — a
        // SEARCH-QUALITY trap of the coarser unit move-set, NOT a structural cost) while
        // the bigint/cache win (-53) holds. Stage 1.5 verdict: atomicity is free;
        // unit-keying is a net-positive search-dynamics lever (net -45), with one
        // residual local-optimum gap addressable by richer unit moves / more budget.
        println!(
            "[GROUP-AB][VERDICT] grouped_better={grouped_better} flat_better={flat_better} \
             equal={equal} checked={checked} flat_nonatomic={flat_nonatomic}/{checked} \
             total_flat={total_flat} total_grouped={total_grouped} net_delta={} \
             (flat optima ~always atomic ⇒ atomicity free; deltas are search-dynamics)",
            total_flat - total_grouped
        );
    }

    #[test]
    #[ignore = "M7 production-baseline corpus comparison; release + python-free; run with --ignored"]
    fn real_all_22_l0_optimized_vs_production_baseline() {
        use crate::s3_gap::floor::dag_traffic_floor;
        use crate::s3_gap::instance::extract_instance;

        // M7: attempt to close the M6 caveat by comparing the optimizer to the REAL
        // PRODUCTION residency scheduler (identity root order + Belady-ish eviction),
        // whose width-weighted DRAM traffic comes from `compile_layer().stats.dram_traffic`.
        //
        // FINDING (the reason this test does not claim "beats production"): production's
        // `dram_traffic` is NOT directly comparable to the scorer/oracle/floor metric, and
        // the two count fundamentally DIFFERENT things:
        //   - scorer/oracle/floor: each DISTINCT reachable `Read` leaf counted ONCE at its
        //     DAG width (+ modeled reloads on eviction); Prior/VirtualSetup excluded.
        //   - production: each Global read operand the COMPILED PROGRAM actually emits,
        //     which is residency/alias/fusion dependent (a leaf may be re-read across
        //     roots, or never separately loaded).
        // Measured proof these are different metrics — the sign of (prod - floor) FLIPS
        // across no-caches fixtures: bigint prod=119 < floor=157 (production emits fewer
        // loads than there are distinct leaves), yet mem_word_only prod=53 > floor=35
        // (production RE-reads base leaves it didn't keep resident). All reads here are
        // base mem/witness — NOT scratch and NOT resolver (an earlier guess of mine,
        // disproven by a read-place breakdown). So the prod-vs-opt deltas below are NOT a
        // valid beats-production claim. This test DOCUMENTS the gap (classifying each
        // fixture comparable/not by the floor guard) and asserts only the genuine scorer
        // invariant `opt >= floor`. Closing the caveat needs the scorer to count what the
        // compiled program actually reads (or to score candidates via `compile_layer`).
        const POPULATION: usize = 200;
        const EVAL_BUDGET: usize = 2_000;
        const FINAL_STARTS: usize = 4;
        const FINAL_EVAL_BUDGET: usize = 500;

        let mut checked = 0usize;
        let mut comparable = 0usize;
        let mut not_comparable = 0usize;
        for &fixture in ALL_22_L0_FIXTURES {
            let name = fixture
                .trim_end_matches("_layout_gkr.json")
                .trim_end_matches("_layout_no_caches_gkr.json");
            let Some((layer, cross)) = crate::try_load_l0(fixture) else {
                println!("[M7] {name:<48} LOAD_FAILED");
                continue;
            };
            let Some(prod) = crate::production_l0_traffic(fixture, crate::REAL_BUDGET) else {
                println!(
                    "[M7] {name:<48} PROD_COMPILE_FAILED (budget {})",
                    crate::REAL_BUDGET
                );
                continue;
            };
            let inst = extract_instance(&layer, &cross, crate::REAL_BUDGET);
            let sites = enumerate_demand_sites(&inst);
            if inst.roots.is_empty() || sites.is_empty() {
                continue;
            }
            let floor = dag_traffic_floor(&layer, &cross) as u64;
            let smoke = compact_smoke(
                &inst,
                &sites,
                POPULATION,
                EVAL_BUDGET,
                FINAL_STARTS,
                FINAL_EVAL_BUDGET,
            );
            let opt = smoke
                .optimized
                .best_score
                .traffic
                .min(smoke.final_states.best.traffic);
            // The scorer/floor share one model, so this is a genuine invariant.
            assert!(
                opt >= floor,
                "{name}: optimizer traffic {opt} below DAG floor {floor}"
            );
            // Comparability: production cannot read below the distinct-leaf floor IF it
            // counted traffic the same way the scorer does. `prod < floor` proves the two
            // metrics diverge for this fixture → its prod-vs-opt delta is meaningless.
            let comparable_here = prod >= floor;
            if comparable_here {
                comparable += 1;
            } else {
                not_comparable += 1;
            }
            let vs_prod = prod as i64 - opt as i64;
            println!(
                "[M7] {name:<48} floor={floor:<5} prod={prod:<5} optimized={opt:<5} vs_prod={vs_prod} \
                 comparable={comparable_here}"
            );
            checked += 1;
        }
        assert!(checked > 0, "no fixtures checked — corpus setup broken");
        println!(
            "[M7][VERDICT] production baseline is COMPUTABLE (compile_layer.dram_traffic) but NOT \
             metric-comparable to the scorer: {not_comparable}/{checked} fixtures have prod < floor \
             (proof the metrics differ — the scorer counts distinct reachable leaves, production counts \
             emitted loads; the sign of prod-floor flips across fixtures). {comparable} pass the floor \
             guard but still differ on emitted-vs-reachable accounting. CONCLUSION: closing the M6 caveat \
             needs the scorer to count what the COMPILED PROGRAM actually reads (residency/alias/fusion- \
             aware), or to score candidates via compile_layer. M6-vs-neutral stands."
        );
    }

    #[test]
    #[ignore = "research invariant: every L0 layout is feasible at budget 8 under any root order"]
    fn real_all_22_l0_feasible_at_budget_8_under_any_order() {
        use crate::s3_gap::instance::extract_instance;

        // The real compiler materializes these L0 layers at a working set of 8 cells.
        // Under the corrected single-accumulator streaming model the scorer must agree:
        // every cone's spill-peak fits budget 8, so the layout is schedulable. Because
        // the cone-fit gate can evict ALL outsiders at a root's start (nothing is
        // borrowed yet), `max cone spill-peak <= budget` is a candidate-INDEPENDENT
        // guarantee of feasibility under ANY root order — which we also check directly
        // with the neutral order plus seeded random orders.
        const BUDGET: usize = 8;
        const SEEDS: u64 = 16;

        let mut checked = 0usize;
        let mut offenders: Vec<(String, u32)> = Vec::new();
        for &fixture in ALL_22_L0_FIXTURES {
            let name = fixture
                .trim_end_matches("_layout_gkr.json")
                .trim_end_matches("_layout_no_caches_gkr.json");
            let flavor = if fixture.contains("no_caches") {
                "no-cache"
            } else {
                "cache"
            };
            let label = format!("{name}/{flavor}");
            let Some((layer, cross)) = crate::try_load_l0(fixture) else {
                println!("[FEAS-8] {label:<52} LOAD_FAILED");
                continue;
            };
            let inst = extract_instance(&layer, &cross, BUDGET);
            let sites = enumerate_demand_sites(&inst);
            if inst.roots.is_empty() || sites.is_empty() {
                println!("[FEAS-8] {label:<52} SKIP (empty)");
                continue;
            }

            let fi = crate::s3_planner::forkset::analyze(&inst);
            let max_peak = fi.root_peak.iter().copied().max().unwrap_or(0);
            println!(
                "[FEAS-8] {label:<52} roots={:<4} nodes={:<5} max_cone_peak={max_peak}",
                inst.roots.len(),
                inst.nodes.len(),
            );
            if (max_peak as usize) > BUDGET {
                offenders.push((label.clone(), max_peak));
                continue;
            }

            assert!(
                score_candidate(&inst, &sites, &Genome::neutral(&inst, &sites)).feasible,
                "{label}: neutral root order is infeasible at budget {BUDGET}"
            );
            for seed in 0..SEEDS {
                let genome = deterministic_smoke_genome(&inst, &sites, seed);
                assert!(
                    score_candidate(&inst, &sites, &genome).feasible,
                    "{label}: random root order seed {seed} is infeasible at budget {BUDGET}"
                );
            }
            checked += 1;
        }

        assert!(
            offenders.is_empty(),
            "layouts whose max cone spill-peak exceeds budget {BUDGET}: {offenders:?}"
        );
        assert_eq!(checked, ALL_22_L0_FIXTURES.len());
    }

    /// Min feasible `(traffic, instrs)` the scorer reaches over the neutral order
    /// plus `seeds` random-key genomes (random root order + admit/recovery/keep
    /// biases). `None` if no genome is feasible. This is the scorer's
    /// best-over-orders, the analogue of the oracle's free-permutation (Mode J)
    /// search — both optimize order AND eviction jointly.
    fn scorer_best_over_orders(inst: &OracleInstance, seeds: u64) -> Option<(u64, u64)> {
        let sites = enumerate_demand_sites(inst);
        let mut best: Option<(u64, u64)> = None;
        let neutral = score_candidate(inst, &sites, &Genome::neutral(inst, &sites));
        if neutral.feasible {
            best = Some((neutral.traffic, neutral.instrs));
        }
        for seed in 0..seeds {
            let g = deterministic_smoke_genome(inst, &sites, seed);
            let s = score_candidate(inst, &sites, &g);
            if s.feasible {
                let o = (s.traffic, s.instrs);
                best = Some(best.map_or(o, |b| b.min(o)));
            }
        }
        best
    }

    fn seed12_instance(budget: usize) -> OracleInstance {
        // Two shared forks (Add{2}, Mul{3}) over reads {0,1}; reordering + caching
        // both forks vs reloading reads trade off with the budget.
        OracleInstance {
            budget,
            reloadable_values: vec![],
            roots: vec![4, 5, 6],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![1, 0]),
                n(3, NodeKind::Mul, 1, false, vec![0, 1]),
                n(4, NodeKind::Add, 1, false, vec![0, 2]),
                n(5, NodeKind::Mul, 1, false, vec![3, 0]),
                n(6, NodeKind::Mul, 1, false, vec![2, 3]),
            ],
        }
    }

    /// Distinct recomputable (Add/Mul/Special) node count — the minimum number of
    /// instrs any schedule must execute, since each such node's value is needed by
    /// some root and must be computed at least once (caching makes it exactly once;
    /// recomputation makes it more). The instr analogue of the read-place floor.
    fn distinct_recomputable_floor(inst: &OracleInstance) -> u64 {
        inst.nodes
            .iter()
            .filter(|nd| matches!(nd.kind, NodeKind::Add | NodeKind::Mul | NodeKind::Special))
            .count() as u64
    }

    #[test]
    fn scorer_instrs_never_below_distinct_recomputable_floor() {
        // L4: the secondary (instr) objective has a lower bound analogous to the read
        // floor — total instrs can never drop below the count of distinct recomputable
        // nodes. Checked on a multi-fork eviction-pressured instance (seed12, budget 3)
        // across the neutral order plus random orders/biases.
        let inst = seed12_instance(3);
        let sites = enumerate_demand_sites(&inst);
        let floor = distinct_recomputable_floor(&inst);
        assert_eq!(floor, 5, "seed12 has 5 distinct Add/Mul nodes");

        let neutral = score_candidate(&inst, &sites, &Genome::neutral(&inst, &sites));
        assert!(
            neutral.instrs >= floor,
            "neutral instrs {} below floor {floor}",
            neutral.instrs
        );
        for seed in 0..128u64 {
            let g = deterministic_smoke_genome(&inst, &sites, seed);
            let s = score_candidate(&inst, &sites, &g);
            if s.feasible {
                assert!(
                    s.instrs >= floor,
                    "seed {seed} instrs {} below floor {floor}",
                    s.instrs
                );
            }
        }
    }

    #[test]
    fn scorer_instrs_floor_is_tight_when_all_forks_cacheable() {
        // At a generous budget every shared fork is cacheable, so the min-traffic
        // schedule also computes each recomputable node exactly once → the best
        // (traffic, instrs) lands its instr count exactly on the distinct floor.
        let inst = seed12_instance(16);
        let floor = distinct_recomputable_floor(&inst);
        let best = scorer_best_over_orders(&inst, 256).expect("feasible at budget 16");
        assert_eq!(best.1, floor, "best instrs must hit the floor when all forks fit");
    }

    /// H1+M5 differential (the keystone validation of the scorer's cost model):
    /// the scorer's best-over-orders must equal the EXACT global optimum the CP-SAT
    /// oracle proves under free permutation (Mode J). The `>=` direction is the
    /// soundness guard — a scorer schedule can never cost LESS than the proven
    /// optimum; if it did, the scorer would be under-counting (modeling an
    /// impossible schedule as feasible). The `==` direction shows the random-key
    /// decoder actually reaches the optimum on these tractable multi-root cones.
    #[test]
    #[ignore = "requires python3 + ortools"]
    fn scorer_best_over_orders_matches_oracle_j() {
        use crate::s3_gap::driver::{oracle_available, run_oracle, Mode};
        if !oracle_available() {
            eprintln!("ortools unavailable; skipping");
            return;
        }
        const SEEDS: u64 = 512;
        let cases: Vec<(&str, OracleInstance)> = vec![
            ("seed12(b3)", seed12_instance(3)),
            (
                "carry(b4)",
                OracleInstance {
                    budget: 4,
                    reloadable_values: vec![],
                    roots: vec![2, 3, 4],
                    nodes: vec![
                        n(0, NodeKind::Read, 4, true, vec![]),
                        n(1, NodeKind::Read, 4, true, vec![]),
                        n(2, NodeKind::Add, 4, false, vec![0]),
                        n(3, NodeKind::Add, 4, false, vec![1]),
                        n(4, NodeKind::Add, 4, false, vec![0]),
                    ],
                },
            ),
            (
                // (C) binds at b1 under a fixed order, but the scorer reorders the
                // two X-consumers adjacent and puts the fold-of-folds last → traffic
                // 3 (oracle-E fixed-order is 4; oracle-J free-permutation is 3).
                "fold_of_folds(b1)",
                OracleInstance {
                    budget: 1,
                    reloadable_values: vec![],
                    roots: vec![3, 6, 7],
                    nodes: vec![
                        n(0, NodeKind::Read, 1, true, vec![]),
                        n(1, NodeKind::Read, 1, true, vec![]),
                        n(2, NodeKind::Read, 1, true, vec![]),
                        n(3, NodeKind::Add, 1, false, vec![0]),
                        n(4, NodeKind::Add, 1, false, vec![1]),
                        n(5, NodeKind::Add, 1, false, vec![2]),
                        n(6, NodeKind::Add, 1, false, vec![4, 5]),
                        n(7, NodeKind::Add, 1, false, vec![0]),
                    ],
                },
            ),
            (
                "shared_product(b16)",
                OracleInstance {
                    budget: 16,
                    reloadable_values: vec![],
                    roots: vec![3, 4],
                    nodes: vec![
                        n(0, NodeKind::Read, 1, true, vec![]),
                        n(1, NodeKind::Read, 1, true, vec![]),
                        n(2, NodeKind::Mul, 1, false, vec![0, 1]),
                        n(3, NodeKind::Add, 1, false, vec![2, 0]),
                        n(4, NodeKind::Add, 1, false, vec![2, 1]),
                    ],
                },
            ),
        ];

        for (label, inst) in &cases {
            let e = run_oracle(inst, Mode::J, 0.0, 60).unwrap();
            assert_eq!(e.status, "optimal", "{label}: oracle-J not optimal");
            let oracle = (e.traffic, e.instrs);
            let best = scorer_best_over_orders(inst, SEEDS)
                .unwrap_or_else(|| panic!("{label}: scorer found NO feasible genome"));
            assert!(
                best >= oracle,
                "{label}: scorer best {best:?} < oracle-J {oracle:?} — UNSOUND (under-count)"
            );
            assert_eq!(best, oracle, "{label}: scorer best {best:?} != oracle-J {oracle:?}");
        }
    }

    /// Budget sweep: across the feasibility range the scorer best-over-orders tracks
    /// oracle-J. seed12 traffic falls 4→2 (b1→b2) and instrs 6→5 (b2→b3) as the
    /// budget admits more fork caching.
    ///
    /// SOUNDNESS (`>=`) is the hard invariant at EVERY budget: the scorer's cost
    /// model never reports a schedule cheaper than the proven global optimum — if it
    /// did, it would be under-counting (an impossible schedule scored feasible). The
    /// optimizer can only ever be misled by an under-count, so this is the direction
    /// that matters for correctness; it holds everywhere here.
    ///
    /// TIGHTNESS (`==`) holds for budget >= 2. At budget 1 (a single cell — outside
    /// the real regime, where the corpus floors at peak 8 under budget 16) the greedy
    /// single-cell residency model floors at traffic 5 while oracle-J recomputes a
    /// fork to reach traffic 4. Confirmed a REPRESENTABILITY gap, not a search gap
    /// (the optimum is unreached over 50k random genomes), and in the SAFE direction
    /// (the scorer over-counts, never under-counts). Documented, not asserted away.
    #[test]
    #[ignore = "requires python3 + ortools"]
    fn scorer_budget_sweep_matches_oracle_j() {
        use crate::s3_gap::driver::{oracle_available, run_oracle, Mode};
        if !oracle_available() {
            eprintln!("ortools unavailable; skipping");
            return;
        }
        const SEEDS: u64 = 512;
        for budget in 1..=4usize {
            let inst = seed12_instance(budget);
            let e = run_oracle(&inst, Mode::J, 0.0, 60).unwrap();
            assert_eq!(e.status, "optimal", "seed12 b{budget}: oracle-J not optimal");
            let oracle = (e.traffic, e.instrs);
            let best = scorer_best_over_orders(&inst, SEEDS)
                .unwrap_or_else(|| panic!("seed12 b{budget}: scorer found NO feasible genome"));
            assert!(
                best >= oracle,
                "seed12 b{budget}: scorer best {best:?} < oracle-J {oracle:?} — UNSOUND"
            );
            if budget >= 2 {
                assert_eq!(
                    best, oracle,
                    "seed12 b{budget}: scorer best {best:?} != oracle-J {oracle:?}"
                );
            }
        }
    }
}
