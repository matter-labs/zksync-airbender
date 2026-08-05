//! Forward execution contract dag_ir arithmetic does not carry (spec §10) + output model.

use super::binding::{BackingTable, SourceWindowTable};
use super::error::CompileError;
use super::isa::{OperandLine, Program};
use super::source::{ConstBank, DerivedE4Banks, SpecialTable};
use super::stats::CompileStats;
use gkr_eval_ir::{
    DagLayer, Expr, ExprId, Ext, FieldKind, ReadPlace, RootExecution, RootId, SinkInfo, SinkKind,
    SourceKind,
};
use std::collections::{BTreeMap, HashMap};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForwardAction {
    Compute,
    CopyAlias { src: ReadPlace, dst: SinkInfo }, // storage view alias (no kernel work)
    SkipScratchPrefill,                          // emit nothing; excluded from value parity
}

#[derive(Clone, Debug, Default)]
pub struct DagForwardContext {
    pub specials: SpecialTable,
    pub consts: ConstBank,
    pub derived_e4: DerivedE4Banks,
    pub backings: BackingTable,
    /// Final program-local source-window geometry. Program source lanes index this table.
    pub source_windows: SourceWindowTable,
    pub actions: HashMap<RootId, ForwardAction>,
    /// Each cache (materialization-only) root → the backing `(slot, col)` it materialized to.
    /// Same-layer reuse of a cached value is now a shared `ExprId` the forward DFS
    /// recomputes (Part B), so this is kept only as the cache root's materialize record.
    pub cache_loc: HashMap<RootId, (u8, u16)>,
    /// Cross-layer field map (codex Imp2): each prior-layer `ReadPlace::{LayerOutput,
    /// CacheOutput}` → the TRUE field of its producing sink. `child_operand_field`
    /// consults this to label a cross-layer read with its producing-sink field rather
    /// than the enclosing reduction's field. Built once per circuit by
    /// `build_cross_layer_field_map` and cloned into the ctx at the top of
    /// `compile_layer`. Empty by default (single-layer tests have no cross-layer reads).
    pub cross_layer_fields: HashMap<ReadPlace, FieldKind>,
}

/// What the interpreter produces per row: each materialized root's value.
#[derive(Clone, Debug, Default)]
pub struct RowOutputs {
    pub by_root: HashMap<RootId, Ext>,
}

/// Where a Compute root's final value lands in the executed program.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutputCell {
    Smem(u16),
    Global { slot: u8, col: u16 },
}

/// How a root's value is obtained after running the program.
/// `Cell` = written by the encoded `Program` (Compute roots).
/// `Alias` = resolved by the CPU action executor OUTSIDE the ISA stream
/// (CopyAlias roots — zero program lanes, per spec §10 "not kernel bytecode").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RootOutput {
    Cell(OutputCell),
    Alias(OperandLine),
}

#[derive(Clone, Debug, Default)]
pub struct CompileTrace {
    pub reached_lookup_leaves: Vec<ExprId>, // LookupValue leaves emitted-code reached (must be covered)
    pub pruned_resolution_exprs: Vec<ExprId>, // exprs pruned because they carry a ResolutionStrategy
    pub max_live_cells: usize,
    pub nested_subexprs: usize, // compound children lowered to a cell (§11 general fallback)
    /// v2 per-cell placed-width map retained from `Placement` (Task 6): `(program
    /// instruction index, bf-lane index) → placed width` of the value live in that lane
    /// at that instruction; an Ext entry covers all 4 lanes of its bucket. Consumed by
    /// `validate::check_smem_region_agreement` (`SmemRegionMismatch`), which needs it
    /// AFTER `placement.cell_of` is consumed by materialization and dropped. It rides
    /// `CompileTrace` (rather than a new `CompiledLayer` field) because the trace is
    /// `Default`-able: hand-built test layers get an EMPTY map, which the validator
    /// treats as "no placement metadata — skip", the same convention
    /// `check_field_storage_agreement` uses for slots absent from the backing table.
    pub placed_cell_fields: std::collections::HashMap<(usize, u16), super::isa::OperandField>,
}

#[derive(Clone, Debug)]
pub struct CompiledLayer {
    pub program: Program,
    pub ctx: DagForwardContext,
    pub root_outputs: Vec<(RootId, RootOutput)>, // Compute (Cell) + CopyAlias (Alias) roots
    pub skipped: Vec<RootId>,                    // SkipScratchPrefill roots
    pub trace: CompileTrace,
    /// Smem budget in BF LANES (4-B cells), the allocator's internal unit — 16 at the
    /// committed b16 corpus. On the v2 wire the same space is `budget / 4` ext-cell
    /// BUCKETS ([`Self::budget_buckets`]); bf-field `Smem` indices are lane indices
    /// bounded by `budget`, ext-field indices are bucket indices bounded by
    /// `budget_buckets()` (spec §3: one number, two views).
    pub budget: usize,
    pub stats: CompileStats,
    /// Stage-3 (schedule-driven) EXPLICIT per-step residency boundary snapshots,
    /// index-aligned with `LayerSchedule::order`: `(before, after)` where `before`
    /// is the realized resident set entering step `p` (after implicit cone-fit drops)
    /// and `after` the realized set leaving it, filtered to real scheduled `ExprId`s
    /// (internal lowering temporaries excluded). Empty for layers built by the old
    /// residency-coupled `compile_layer` path.
    pub resident_realized: Vec<(Vec<ExprId>, Vec<ExprId>)>,
}

impl CompiledLayer {
    pub fn instructions(&self) -> &[super::isa::Instr] {
        &self.program.instrs
    }

    /// The smem budget in v2 ext-cell BUCKETS (16 B × blockDim each): `budget / 4`.
    /// The bound for ext-field `Smem` wire indices (bf indices are bounded by
    /// [`Self::budget`] directly).
    pub fn budget_buckets(&self) -> usize {
        self.budget / 4
    }
}

/// Classify every materialize-bearing root directly from canonical DAG semantics.
pub fn build_forward_actions(
    layer: &DagLayer,
    execution: Option<&BTreeMap<RootId, RootExecution>>,
) -> Result<HashMap<RootId, ForwardAction>, CompileError> {
    let mut actions = HashMap::new();
    for (idx, root) in layer.roots.iter().enumerate() {
        // A claim-only (Constraint) root never materializes — ignored for forward.
        if root.materialize.is_none() {
            continue;
        }
        let rid = RootId(idx as u32);
        let action = match execution.and_then(|entries| entries.get(&rid)) {
            Some(RootExecution::Alias { source }) => ForwardAction::CopyAlias {
                src: source.clone(),
                dst: root.materialize.clone().expect("alias root has a sink"),
            },
            Some(RootExecution::Preinitialized) => ForwardAction::SkipScratchPrefill,
            None => match root.claim.as_ref() {
                None => ForwardAction::Compute, // cache root (materialization-only)
                Some(_) => classify_claim_root(layer, rid)?,
            },
        };
        actions.insert(rid, action);
    }
    Ok(actions)
}

fn classify_claim_root(layer: &DagLayer, rid: RootId) -> Result<ForwardAction, CompileError> {
    let root = &layer.roots[rid.0 as usize];
    let sink = root
        .materialize
        .as_ref()
        .expect("claim-bearing forward root has a materialization sink");

    if matches!(sink.kind, SinkKind::Scratch { .. }) {
        return Ok(ForwardAction::SkipScratchPrefill);
    }

    let Expr::Source(source) = &layer.exprs[root.expr.0 as usize] else {
        return Ok(ForwardAction::Compute);
    };
    match &layer.sources[source.0 as usize].kind {
        SourceKind::Read { place } => Ok(ForwardAction::CopyAlias {
            src: place.clone(),
            dst: sink.clone(),
        }),
        _ => Ok(ForwardAction::Compute),
    }
}
