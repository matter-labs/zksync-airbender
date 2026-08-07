//! Compile-in-loop fitness scoring.

use std::collections::HashMap;

use gkr_eval_ir::{DagCircuit, DagLayer, FieldKind, ReadPlace};

use crate::forward::artifact::{
    atom_order, relation_units, ForwardLayerArtifact, RelationUnit, SiteKey,
};
use crate::forward::compile::compile_layer;
use crate::forward::compile::decisions::enumerate_site_domain;
use crate::forward::error::CompileError;

use super::genome::{decode_unit_order, Genome};

pub(super) struct LayerCtx<'a> {
    pub layer: &'a DagLayer,
    pub cross_layer_fields: &'a HashMap<ReadPlace, FieldKind>,
    pub budget: usize,
    pub units: Vec<RelationUnit>,
    pub sites: Vec<SiteKey>,
    pub floor: usize,
}

impl<'a> LayerCtx<'a> {
    pub(super) fn new(
        dag: &'a DagCircuit,
        layer_index: usize,
        cross_layer_fields: &'a HashMap<ReadPlace, FieldKind>,
        budget: usize,
    ) -> Self {
        let layer = &dag.layers[layer_index];
        let compute_roots = crate::forward::context::build_compute_roots(layer);
        let floor = super::floor::dag_traffic_floor(layer, cross_layer_fields, &compute_roots);
        let units = relation_units(layer);
        let order = atom_order(layer, &units);
        Self {
            layer,
            cross_layer_fields,
            budget,
            units,
            sites: enumerate_site_domain(layer, &order, &compute_roots)
                .into_iter()
                .collect(),
            floor,
        }
    }

    pub(super) fn n_order_keys(&self) -> usize {
        self.units.len()
    }

    pub(super) fn n_sites(&self) -> usize {
        self.sites.len()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct CandidateScore {
    pub infeasible: bool,
    pub dram_traffic: usize,
    pub instrs: usize,
}

pub(super) fn decode_schedule(genome: &Genome, ctx: &LayerCtx) -> ForwardLayerArtifact {
    assert_eq!(
        genome.cache_priority.len(),
        ctx.sites.len(),
        "genome cache_priority length must match ctx site domain"
    );
    assert_eq!(
        genome.root_order_key.len(),
        ctx.units.len(),
        "genome root_order_key length must match ctx units"
    );
    let unit_perm = decode_unit_order(&genome.root_order_key);
    let units: Vec<RelationUnit> = unit_perm.iter().map(|&u| ctx.units[u].clone()).collect();
    let sites: Vec<(SiteKey, f64)> = ctx
        .sites
        .iter()
        .copied()
        .zip(genome.cache_priority.iter().copied())
        .collect();
    ForwardLayerArtifact {
        units,
        sites,
        predicted_traffic: 0,
    }
}

pub(super) fn genome_from_schedule(ls: &ForwardLayerArtifact, ctx: &LayerCtx) -> Genome {
    use std::collections::HashMap;
    let canon_idx: HashMap<(gkr_eval_ir::RootGroup, usize), usize> = ctx
        .units
        .iter()
        .enumerate()
        .map(|(i, u)| ((u.group, u.relation_index), i))
        .collect();
    let n = ctx.units.len();
    let denom = n.max(1) as f64;
    let mut root_order_key = vec![0.0f64; n];
    for (rank, u) in ls.units.iter().enumerate() {
        let ci = canon_idx[&(u.group, u.relation_index)];
        root_order_key[ci] = rank as f64 / denom;
    }
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

pub(super) fn score(genome: &Genome, ctx: &LayerCtx) -> CandidateScore {
    let schedule = decode_schedule(genome, ctx);
    match compile_layer(ctx.layer, ctx.cross_layer_fields, &schedule, ctx.budget) {
        Ok(compiled) => CandidateScore {
            infeasible: false,
            dram_traffic: compiled.stats.dram_traffic,
            instrs: compiled.stats.instrs,
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
            ctx.n_order_keys(),
            ctx.sites.len()
        ),
    }
}
