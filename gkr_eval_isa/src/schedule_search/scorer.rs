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

use std::collections::HashMap;

use cs::gkr_compiler::dag_ir::{DagLayer, FieldKind, ReadPlace, RootId, SiteKey};
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
    /// `floor::dag_traffic_floor(layer, cross_layer_fields)` — recorded into the
    /// winning `LayerSchedule`, not used by `score` itself.
    pub floor: usize,
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
    let decisions = SiteDecisions::new(schedule.sites.iter().copied());
    let policy = MaterializePolicy::Decisions { decisions, budget: ctx.budget };
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
