//! Forward execution metadata not carried by the arithmetic DAG.

use super::binding::{BackingTable, SourceWindowTable};
use super::isa::Program;
use super::source::{ConstBank, DerivedE4Banks, SpecialTable};
use super::stats::CompileStats;
use gkr_eval_ir::{DagLayer, RootId};
use std::collections::BTreeSet;

#[derive(Clone, Debug, Default)]
pub(crate) struct DagForwardContext {
    pub specials: SpecialTable,
    pub consts: ConstBank,
    pub derived_e4: DerivedE4Banks,
    pub backings: BackingTable,
    /// Final program-local source-window geometry. Program source lanes index this table.
    pub source_windows: SourceWindowTable,
}

#[derive(Clone, Debug)]
pub struct CompiledLayer {
    pub program: Program,
    pub specials: SpecialTable,
    pub consts: ConstBank,
    pub derived_e4: DerivedE4Banks,
    pub backings: BackingTable,
    pub source_windows: SourceWindowTable,
}

#[derive(Clone, Debug)]
pub(crate) struct CompiledLayerBuild {
    pub program: Program,
    pub ctx: DagForwardContext,
    pub budget_lanes: usize,
    pub stats: CompileStats,
}

impl CompiledLayerBuild {
    pub(crate) fn into_runtime(self) -> CompiledLayer {
        let mut backings = self.ctx.backings;
        backings.strip_indexes();
        CompiledLayer {
            program: self.program,
            specials: self.ctx.specials,
            consts: self.ctx.consts,
            derived_e4: self.ctx.derived_e4,
            backings,
            source_windows: self.ctx.source_windows,
        }
    }
}

/// Classify every materialize-bearing root directly from canonical DAG semantics.
pub(crate) fn build_compute_roots(layer: &DagLayer) -> BTreeSet<RootId> {
    let mut roots = BTreeSet::new();
    for (idx, root) in layer.roots.iter().enumerate() {
        // A claim-only root has no forward materialization.
        if root.materialize.is_none() {
            continue;
        }
        let rid = RootId(idx as u32);
        if !layer.forward_skip_roots.contains(&rid) {
            roots.insert(rid);
        }
    }
    roots
}
