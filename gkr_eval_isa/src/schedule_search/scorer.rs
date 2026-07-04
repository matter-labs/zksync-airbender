//! Compile-in-loop fitness function (Task 6 spec §1): decode a [`Genome`] to a
//! concrete `(order, SiteDecisions)` candidate, compile it for real under
//! `MaterializePolicy::Decisions`, and read the resulting `CandidateScore` off
//! the ACTUAL compiled program — not a simulated replay.
//!
//! This replaces `gkr_eval_isa/tests/s3_planner/metaheuristic.rs`'s
//! `score_candidate`/`Replay` event-simulation engine (deleted, Task 6): that
//! engine modeled admit/evict/reload decisions itself and could drift from what
//! the real emitter (`fwd::compile::lower`) does. `score` has no such model —
//! it IS the real emitter, run once per candidate.

use std::collections::{BTreeMap, HashMap};
use std::sync::Mutex;

use cs::definitions::GKRAddress;
use cs::gkr_compiler::dag_ir::{DagLayer, FieldKind, LayerSchedule, ReadPlace, RootId, SiteKey};
use cs::gkr_compiler::{GKRCircuitArtifact, GKRLayerDescription};
use field::baby_bear::base::BabyBearField;

use crate::fwd::compile::decisions::SiteDecisions;
use crate::fwd::compile::{compile_layer_with_policy, MaterializePolicy};
use crate::fwd::error::CompileError;

use super::decode::decode_order;
use super::genome::Genome;
use super::structure::{enumerate_sites, relation_units};

/// Everything [`score`] needs for one layer at one budget, computed once per
/// layer by the producer (Task 6 §"Producer requirements") and shared across
/// every candidate genome scored against it.
pub struct LayerCtx<'a> {
    pub layer: &'a DagLayer,
    pub artifact_layer: &'a GKRLayerDescription,
    pub scratch_mapping: &'a std::collections::BTreeMap<cs::definitions::GKRAddress, usize>,
    pub cross_layer_fields: &'a HashMap<ReadPlace, FieldKind>,
    pub budget: usize,
    /// Atom-root scheduling units (`structure::relation_units(layer)`); one
    /// [`Genome::root_order_key`] gene per entry.
    pub units: Vec<Vec<RootId>>,
    /// Structural demand-site domain (`structure::enumerate_sites(layer)`); one
    /// [`Genome::cache_priority`] gene per entry, same order.
    pub sites: Vec<SiteKey>,
    /// `floor::dag_traffic_floor_with_actions(layer, cross_layer_fields, actions)` —
    /// recorded into the winning `LayerSchedule`, not used by `score` itself.
    pub floor: usize,
    /// Task 8a memo cache for [`resident_cap_for_order`], keyed by the concrete
    /// root `order` a genome decodes to: many genomes across a search share the
    /// same order (only `cache_priority` genes differ — `Genome::perturb_one_gene`
    /// mutates one gene at a time and there are usually far more sites than
    /// units), so memoizing avoids re-paying the extra `LegacyRecompute` compile
    /// on every rescoring of the same order. `Mutex` (not `RefCell`) because
    /// `score`/`decode_schedule` take `&LayerCtx` shared across candidates AND the
    /// search fans candidates out across threads (`search.rs`'s `scope.spawn`) —
    /// interior mutability only, no effect on the (pure, deterministic) value
    /// computed per key, so lock contention never changes the result.
    resident_cap_cache: Mutex<HashMap<Vec<RootId>, usize>>,
}

impl<'a> LayerCtx<'a> {
    pub fn new(
        layer: &'a DagLayer,
        artifact_layer: &'a GKRLayerDescription,
        artifact: &'a GKRCircuitArtifact<BabyBearField>,
        cross_layer_fields: &'a HashMap<ReadPlace, FieldKind>,
        budget: usize,
    ) -> Self {
        // Action-aware floor (NOT the plain DAG floor): CopyAlias/SkipScratchPrefill
        // roots are never lowered, so their cones must not count toward the bound the
        // producer records against the compile metric — see
        // `floor::dag_traffic_floor_with_actions`'s doc.
        let actions = crate::fwd::context::build_forward_actions(
            layer,
            artifact_layer,
            &artifact.scratch_space_mapping,
        )
        .unwrap_or_else(|e| panic!("LayerCtx::new: build_forward_actions failed: {e:?}"));
        let floor =
            super::floor::dag_traffic_floor_with_actions(layer, cross_layer_fields, &actions);
        Self {
            layer,
            artifact_layer,
            scratch_mapping: &artifact.scratch_space_mapping,
            cross_layer_fields,
            budget,
            units: relation_units(layer),
            sites: enumerate_sites(layer),
            floor,
            resident_cap_cache: Mutex::new(HashMap::new()),
        }
    }

    pub fn n_order_keys(&self) -> usize {
        self.units.len()
    }

    pub fn n_sites(&self) -> usize {
        self.sites.len()
    }

    /// Task 8a: the `Decisions` resident-admission cap for `order` at this ctx's
    /// `budget` (memoized — see `resident_cap_cache`'s doc). See
    /// [`resident_cap_for_order`] for the derivation.
    pub fn resident_cap(&self, order: &[RootId]) -> usize {
        if let Some(&cap) = self.resident_cap_cache.lock().unwrap().get(order) {
            return cap;
        }
        let cap = resident_cap_for_order(
            self.layer,
            self.artifact_layer,
            self.scratch_mapping,
            self.cross_layer_fields,
            order,
            self.budget,
        );
        self.resident_cap_cache.lock().unwrap().insert(order.to_vec(), cap);
        cap
    }
}

/// Task 8a: `Decisions`' resident-admission budget declines below the full
/// placement `budget` by the COMPUTE HEADROOM `(layer, order)` needs — the
/// placement floor of the exact same layer/order compiled under pure
/// `MaterializePolicy::LegacyRecompute` (no residency at all). Rationale (see
/// `.superpowers/sdd/task-8-report.md`'s Step-0 probes): `try_admit` cannot
/// decline an admission while resident capacity is free, so an uncapped
/// resident set greedily fills the WHOLE placement budget and starves the
/// concurrent evaluation temps `plan_placement` must also fit in the same
/// cells — that is exactly the b16 `BudgetBelowFloor` regression. Capping
/// residents at `budget - legacy_floor` guarantees residents only ever
/// consume cells pure recomputation didn't need; at `cap == 0` `Decisions`
/// degenerates gracefully to `LegacyRecompute`'s own feasibility (no partial
/// admission is possible below width 1 anyway).
///
/// `legacy_floor` is read directly off `Placement::max_live_cells` (via
/// `CompileStats::max_live_cells`) from a real compile at `budget` under
/// `LegacyRecompute` — the ACTUAL peak live-cell width that schedule uses,
/// not a binary-searched approximation. If even `LegacyRecompute` doesn't fit
/// `budget` (should not happen for any budget this producer is ever run at,
/// per the Step-0 probes showing legacy feasible from budget 8), the reported
/// `CompileError::BudgetBelowFloor::floor` is used as a (necessarily
/// conservative — it's only the pressure point nearest instr 0) headroom
/// estimate, which saturates the cap to 0 (full `LegacyRecompute` fallback).
///
/// Deterministic: a pure function of `(layer, order, budget)` (`LegacyRecompute`
/// has no genome/priority dependence at all).
pub fn resident_cap_for_order(
    layer: &DagLayer,
    artifact_layer: &GKRLayerDescription,
    scratch_mapping: &BTreeMap<GKRAddress, usize>,
    cross_layer_fields: &HashMap<ReadPlace, FieldKind>,
    order: &[RootId],
    budget: usize,
) -> usize {
    let legacy_schedule =
        LayerSchedule { order: order.to_vec(), sites: Vec::new(), predicted_traffic: 0, floor: 0 };
    let legacy_floor = match compile_layer_with_policy(
        layer,
        artifact_layer,
        scratch_mapping,
        cross_layer_fields,
        &legacy_schedule,
        budget,
        MaterializePolicy::LegacyRecompute,
    ) {
        Ok(compiled) => compiled.stats.max_live_cells,
        Err(CompileError::BudgetBelowFloor { floor, .. }) => floor,
        Err(e) => panic!(
            "resident_cap_for_order: unexpected LegacyRecompute compile error {:?} (order len={})",
            e,
            order.len()
        ),
    };
    budget.saturating_sub(legacy_floor)
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
pub fn decode_schedule(genome: &Genome, ctx: &LayerCtx) -> cs::gkr_compiler::dag_ir::LayerSchedule {
    assert_eq!(
        genome.cache_priority.len(),
        ctx.sites.len(),
        "genome cache_priority length must match ctx site domain"
    );
    let order = decode_order(&genome.root_order_key, &ctx.units);
    let sites: Vec<(SiteKey, f64)> =
        ctx.sites.iter().copied().zip(genome.cache_priority.iter().copied()).collect();
    cs::gkr_compiler::dag_ir::LayerSchedule { order, sites, predicted_traffic: 0, floor: ctx.floor }
}

/// The fitness function (Task 6 spec §1). Decodes `genome`, compiles it for
/// real under `MaterializePolicy::Decisions`, and reads `CandidateScore` off
/// the compiled program's stats. `Err(CompileError::BudgetBelowFloor)` is the
/// only legitimately-infeasible outcome (not enough budget for this genome's
/// residency choices); ANY other `Err` is a bug in decode/search — not a
/// legitimately-infeasible candidate — so it panics with a genome dump rather
/// than silently ranking the candidate out.
pub fn score(genome: &Genome, ctx: &LayerCtx) -> CandidateScore {
    let schedule = decode_schedule(genome, ctx);
    let resident_cap = ctx.resident_cap(&schedule.order);
    let decisions = SiteDecisions::new(schedule.sites.iter().copied());
    let policy = MaterializePolicy::Decisions { decisions, budget: resident_cap };
    match compile_layer_with_policy(
        ctx.layer,
        ctx.artifact_layer,
        ctx.scratch_mapping,
        ctx.cross_layer_fields,
        &schedule,
        ctx.budget,
        policy,
    ) {
        Ok(compiled) => CandidateScore {
            infeasible: false,
            dram_traffic: compiled.stats.dram_traffic,
            instrs: compiled.stats.program_lanes,
        },
        Err(CompileError::BudgetBelowFloor { .. }) => {
            CandidateScore { infeasible: true, dram_traffic: usize::MAX, instrs: usize::MAX }
        }
        Err(err) => panic!(
            "scorer: unexpected compile error {:?} for genome {:?} (order units={}, sites={})",
            err,
            genome,
            ctx.units.len(),
            ctx.sites.len()
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn objective_key_ranks_infeasible_last_regardless_of_fields() {
        let feasible = CandidateScore { infeasible: false, dram_traffic: usize::MAX, instrs: usize::MAX };
        let infeasible = CandidateScore { infeasible: true, dram_traffic: 0, instrs: 0 };
        assert!(objective_key(&feasible) < objective_key(&infeasible));
        assert!(feasible < infeasible);
    }

    #[test]
    fn candidate_score_orders_by_traffic_then_instrs() {
        let a = CandidateScore { infeasible: false, dram_traffic: 10, instrs: 100 };
        let b = CandidateScore { infeasible: false, dram_traffic: 10, instrs: 50 };
        let c = CandidateScore { infeasible: false, dram_traffic: 5, instrs: 999 };
        assert!(b < a, "lower instrs wins the traffic tie");
        assert!(c < a, "lower traffic always wins regardless of instrs");
    }
}
