//! Compile-in-loop fitness function: decode a [`Genome`] to a
//! concrete `(order, SiteDecisions)` candidate, compile it for real with the
//! decoded `SiteDecisions`, and read the resulting `CandidateScore` off
//! the ACTUAL compiled program — not a simulated replay.
//!
//! There is no separate replay cost model: `score` runs the real emitter once
//! per candidate.

use std::collections::HashMap;

use gkr_eval_ir::{DagCircuit, DagLayer, FieldKind, ReadPlace, RootExecution, RootId};

use crate::forward::compile::compile_layer;
use crate::forward::compile::decisions::SiteDecisions;
use crate::forward::error::CompileError;
use crate::schedule::{LayerSchedule, RelationUnit, SiteKey};

use super::decode::decode_unit_order;
use super::genome::Genome;
use super::structure::enumerate_sites;

/// Everything [`score`] needs for one layer at one budget, computed once per
/// layer by the producer (Task 6 §"Producer requirements") and shared across
/// every candidate genome scored against it.
pub struct LayerCtx<'a> {
    pub layer: &'a DagLayer,
    pub layer_index: usize,
    pub root_execution: Option<&'a std::collections::BTreeMap<RootId, RootExecution>>,
    pub cross_layer_fields: &'a HashMap<ReadPlace, FieldKind>,
    pub budget: usize,
    /// Atom-root scheduling units; one [`Genome::root_order_key`] gene per entry.
    /// Derived as a projection of [`Self::units_with_caches`]
    /// (`u.atom_roots.clone()`), NOT from a separate `relation_units` call, so
    /// `units[i] == units_with_caches[i].atom_roots` holds by construction and the
    /// genome key index `i` maps to the same relation in both (codex-P2).
    pub units: Vec<Vec<RootId>>,
    /// Canonical relation units WITH cache ownership
    /// (`structure::relation_units_with_caches(layer)`) — the single grouping
    /// source. `decode_schedule` reorders these by the genome unit permutation
    /// and clones them into the decoded `LayerSchedule.units`.
    pub units_with_caches: Vec<RelationUnit>,
    /// Structural demand-site domain (`structure::enumerate_sites(layer)`); one
    /// [`Genome::cache_priority`] gene per entry, same order.
    pub sites: Vec<SiteKey>,
    /// `floor::dag_traffic_floor_with_actions(layer, cross_layer_fields, actions)` —
    /// recorded into the winning `LayerSchedule`, not used by `score` itself.
    pub floor: usize,
}

impl<'a> LayerCtx<'a> {
    pub fn new(
        dag: &'a DagCircuit,
        layer_index: usize,
        cross_layer_fields: &'a HashMap<ReadPlace, FieldKind>,
        budget: usize,
    ) -> Self {
        let layer = &dag.layers[layer_index];
        let root_execution = dag.globals.root_execution.get(layer_index);
        // Action-aware floor (NOT the plain DAG floor): CopyAlias/SkipScratchPrefill
        // roots are never lowered, so their cones must not count toward the bound the
        // producer records against the compile metric — see
        // `floor::dag_traffic_floor_with_actions`'s doc.
        let actions = crate::forward::context::build_forward_actions(layer, root_execution)
            .unwrap_or_else(|e| panic!("LayerCtx::new: build_forward_actions failed: {e:?}"));
        let floor =
            super::floor::dag_traffic_floor_with_actions(layer, cross_layer_fields, &actions);
        // Single grouping source (codex-P2): derive the atom-only genome-sizing
        // `units` as a projection of `units_with_caches` so both vectors share
        // one unit order — the same genome always decodes to the same flat atom
        // order.
        let units_with_caches = super::structure::relation_units_with_caches(layer);
        let units: Vec<Vec<RootId>> = units_with_caches
            .iter()
            .map(|u| u.atom_roots.clone())
            .collect();
        Self {
            layer,
            layer_index,
            root_execution,
            cross_layer_fields,
            budget,
            units,
            units_with_caches,
            sites: enumerate_sites(layer),
            floor,
        }
    }

    pub fn n_order_keys(&self) -> usize {
        self.units.len()
    }

    pub fn n_sites(&self) -> usize {
        self.sites.len()
    }
}

/// Lexicographic candidate objective: `infeasible` dominates (any feasible
/// candidate outranks any infeasible one, regardless of traffic/instrs), then
/// `dram_traffic` (the primary objective — Task 6 spec §1), then `instrs` as a
/// tie-break. Field declaration order IS the comparison order (`derive(Ord)`
/// compares fields left-to-right; `false < true` so infeasible sorts last).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CandidateScore {
    pub infeasible: bool,
    pub dram_traffic: usize,
    pub instrs: usize,
}

/// `(u8, usize, usize)` projection of a [`CandidateScore`] for callers that want
/// an explicit tuple key rather than relying on `derive(Ord)` — mirrors the
/// prototype's `objective_key` (metaheuristic.rs:5108).
pub fn objective_key(score: &CandidateScore) -> (u8, usize, usize) {
    (score.infeasible as u8, score.dram_traffic, score.instrs)
}

/// Build the `LayerSchedule` candidate `genome` decodes to (order + per-site
/// priority genes), WITHOUT compiling it. Exposed so the search can compile a
/// winning genome's own schedule once at the end without re-deriving it.
pub fn decode_schedule(genome: &Genome, ctx: &LayerCtx) -> LayerSchedule {
    assert_eq!(
        genome.cache_priority.len(),
        ctx.sites.len(),
        "genome cache_priority length must match ctx site domain"
    );
    assert_eq!(
        genome.root_order_key.len(),
        ctx.units_with_caches.len(),
        "genome root_order_key length must match ctx units"
    );
    let unit_perm = decode_unit_order(&genome.root_order_key);
    let units: Vec<RelationUnit> = unit_perm
        .iter()
        .map(|&u| ctx.units_with_caches[u].clone())
        .collect();
    let sites: Vec<(SiteKey, f64)> = ctx
        .sites
        .iter()
        .copied()
        .zip(genome.cache_priority.iter().copied())
        .collect();
    LayerSchedule {
        units,
        sites,
        predicted_traffic: 0,
        floor: ctx.floor,
    }
}

/// Inverse of [`decode_schedule`] (codex-P1 incumbent seeding): the genome whose
/// decode reproduces `ls` exactly, so scoring it yields `ls`'s own traffic and
/// elitism can never lose the incumbent. Requires `ls`'s sites to equal
/// `ctx.sites` (guaranteed by `validate_circuit_schedule` check b).
pub fn genome_from_schedule(ls: &LayerSchedule, ctx: &LayerCtx) -> Genome {
    use std::collections::HashMap;
    // root_order_key: assign each canonical unit its execution rank (unit vec order in `ls`).
    // Map canonical unit identity -> its index in ctx.units_with_caches.
    let canon_idx: HashMap<(gkr_eval_ir::RootGroup, usize), usize> = ctx
        .units_with_caches
        .iter()
        .enumerate()
        .map(|(i, u)| ((u.group.clone(), u.relation_index), i))
        .collect();
    let n = ctx.units_with_caches.len();
    let denom = n.max(1) as f64;
    let mut root_order_key = vec![0.0f64; n];
    for (rank, u) in ls.units.iter().enumerate() {
        let ci = canon_idx[&(u.group.clone(), u.relation_index)];
        root_order_key[ci] = rank as f64 / denom;
    }
    // cache_priority: incumbent priority per ctx.sites[i] (sites order is the gene order).
    let prio: HashMap<SiteKey, f64> = ls.sites.iter().copied().collect();
    let cache_priority = ctx
        .sites
        .iter()
        .map(|s| prio.get(s).copied().unwrap_or(0.0))
        .collect();
    Genome {
        root_order_key,
        cache_priority,
    }
}

/// The fitness function (Task 6 spec §1). Decodes `genome`, compiles it for
/// real with the decoded `SiteDecisions`, and reads `CandidateScore` off
/// the compiled program's stats. `Err(CompileError::BudgetBelowFloor)` is the
/// only legitimately-infeasible outcome (not enough budget for this genome's
/// residency choices); ANY other `Err` is a bug in decode/search — not a
/// legitimately-infeasible candidate — so it panics with a genome dump rather
/// than silently ranking the candidate out.
pub fn score(genome: &Genome, ctx: &LayerCtx) -> CandidateScore {
    let schedule = decode_schedule(genome, ctx);
    let decisions = SiteDecisions::new(schedule.sites.iter().copied());
    match compile_layer(
        ctx.layer,
        ctx.layer_index,
        ctx.root_execution,
        ctx.cross_layer_fields,
        &schedule,
        ctx.budget,
        Some(&decisions),
    ) {
        Ok(compiled) => CandidateScore {
            infeasible: false,
            dram_traffic: compiled.stats.dram_traffic,
            instrs: compiled.stats.program_lanes,
        },
        Err(CompileError::BudgetBelowFloor { .. }) => CandidateScore {
            infeasible: true,
            dram_traffic: usize::MAX,
            instrs: usize::MAX,
        },
        Err(err) => panic!(
            "scorer: unexpected compile error {:?} for genome {:?} (order units={}, sites={})",
            err,
            genome,
            ctx.units.len(),
            ctx.sites.len()
        ),
    }
}
