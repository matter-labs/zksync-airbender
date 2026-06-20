//! Forward execution contract dag_ir arithmetic does not carry (spec §10) + output model.

use super::binding::BackingTable;
use super::error::CompileError;
use super::isa::{DstLine, OperandLine, Program};
use super::source::{ChallengeBanks, ConstBank, SpecialTable};
use cs::gkr_compiler::dag_ir::{DagLayer, Ext, ExprId, Root, RootGroup, RootId};
use cs::definitions::GKRAddress;
use cs::gkr_compiler::{GKRLayerDescription, NoFieldGKRRelation};
use std::collections::{BTreeMap, HashMap};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForwardAction {
    Compute,
    CopyAlias { src_addr: GKRAddress, dst_addr: GKRAddress }, // storage view alias (no kernel work)
    SkipScratchPrefill,                                       // emit nothing; excluded from value parity
}

#[derive(Clone, Debug, Default)]
pub struct DagForwardContext {
    pub specials: SpecialTable,
    pub consts: ConstBank,
    pub challenges: ChallengeBanks,
    pub backings: BackingTable,
    pub actions: HashMap<RootId, ForwardAction>,
    /// Each cache (materialization-only) root → the backing `(slot, col)` it materialized to.
    /// `SourceKind::Prior{id}` re-reads `cache_loc[id]` by default; the scheduler MAY instead
    /// keep a heavily-reused cache resident in an smem cell (an OPTIONAL optimization).
    pub cache_loc: HashMap<RootId, (u8, u16)>,
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
    pub reached_lookup_leaves: Vec<ExprId>,   // LookupValue leaves emitted-code reached (must be covered)
    pub pruned_resolution_exprs: Vec<ExprId>, // exprs pruned because they carry a ResolutionStrategy
    pub max_live_cells: usize,
}

#[derive(Clone, Debug)]
pub struct CompiledLayer {
    pub program: Program,
    pub ctx: DagForwardContext,
    pub root_outputs: Vec<(RootId, RootOutput)>, // Compute (Cell) + CopyAlias (Alias) roots
    pub skipped: Vec<RootId>,                    // SkipScratchPrefill roots
    pub trace: CompileTrace,
    pub budget: usize,
}

/// Classify every `Root::Output` of a layer (spec §10). No closures — real metadata.
/// `artifact_layer` is `artifact.layers[layer_idx]`; `scratch_mapping` is `artifact.scratch_space_mapping`.
pub fn build_forward_actions(
    layer: &DagLayer,
    artifact_layer: &GKRLayerDescription,
    scratch_mapping: &BTreeMap<GKRAddress, usize>,
) -> Result<HashMap<RootId, ForwardAction>, CompileError> {
    let mut actions = HashMap::new();
    for (idx, root) in layer.roots.iter().enumerate() {
        let Root::Output { .. } = root else { continue; }; // Constraint roots ignored for forward
        let rid = RootId(idx as u32);
        let action = match layer.origins.get(&rid) {
            None => ForwardAction::Compute, // cache root (materialization-only)
            Some(origin) => {
                let gates = match origin.group {
                    RootGroup::Gates => &artifact_layer.gates,
                    RootGroup::GatesExternal => &artifact_layer.gates_with_external_connections,
                };
                let relation = &gates[origin.relation_index].enforced_relation;
                classify_relation(rid, relation, scratch_mapping)?
            }
        };
        actions.insert(rid, action);
    }
    Ok(actions)
}

fn classify_relation(
    rid: RootId,
    relation: &NoFieldGKRRelation,
    scratch_mapping: &BTreeMap<GKRAddress, usize>,
) -> Result<ForwardAction, CompileError> {
    match relation {
        NoFieldGKRRelation::MaxQuadratic { output, .. } => {
            if scratch_mapping.contains_key(output) {
                Ok(ForwardAction::SkipScratchPrefill)
            } else {
                Err(CompileError::NonScratchMaxQuadratic(rid))
            }
        }
        NoFieldGKRRelation::CopyInBaseField { input, output }
        | NoFieldGKRRelation::CopyInExtensionField { input, output } => {
            Ok(ForwardAction::CopyAlias { src_addr: *input, dst_addr: *output })
        }
        _ => Ok(ForwardAction::Compute),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cs::definitions::GKRAddress;
    use cs::gkr_compiler::{
        GateArtifacts, GKRLayerDescription, NoFieldGKRRelation,
        NoFieldMaxQuadraticGKRRelation, NoFieldStructuredExpression,
    };
    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, DagLayer, Root, RootGroup, RootId, RootOrigin, RootSlot,
        SinkInfo, SinkKind, FieldKind, SourceInfo, SourceKind,
    };
    use std::collections::BTreeMap;

    // ── helpers ──────────────────────────────────────────────────────────────

    fn empty_layer() -> DagLayer {
        DagLayer {
            sources: vec![],
            exprs: vec![],
            roots: vec![],
            sinks: vec![],
            batching: BatchingOrder { roots: vec![] },
            origins: BTreeMap::new(),
            resolutions: BTreeMap::new(),
        }
    }

    fn min_max_quadratic_relation(output: GKRAddress) -> NoFieldGKRRelation {
        let input = NoFieldMaxQuadraticGKRRelation {
            quadratic_terms: Box::new([]),
            linear_terms: Box::new([]),
            constant: 0,
        };
        NoFieldGKRRelation::MaxQuadratic {
            input,
            expression: NoFieldStructuredExpression::Constant(0),
            output,
        }
    }

    fn make_artifact_layer(relations: Vec<NoFieldGKRRelation>) -> GKRLayerDescription {
        let gates: Vec<GateArtifacts> = relations
            .into_iter()
            .map(|r| GateArtifacts { output_layer: 0, enforced_relation: r })
            .collect();
        GKRLayerDescription {
            layer: 0,
            gates,
            gates_with_external_connections: vec![],
            cached_relations: BTreeMap::new(),
            intermediate_layer_width: None,
        }
    }

    // ── classify_relation: CopyInBaseField ───────────────────────────────────

    #[test]
    fn copy_in_base_field_yields_copy_alias() {
        let src = GKRAddress::ScratchSpace(0);
        let dst = GKRAddress::ScratchSpace(1);
        let relation = NoFieldGKRRelation::CopyInBaseField { input: src, output: dst };
        let mapping = BTreeMap::new();
        let action = classify_relation(RootId(0), &relation, &mapping).unwrap();
        assert_eq!(action, ForwardAction::CopyAlias { src_addr: src, dst_addr: dst });
    }

    // ── classify_relation: CopyInExtensionField ──────────────────────────────

    #[test]
    fn copy_in_extension_field_yields_copy_alias() {
        let src = GKRAddress::InnerLayer { layer: 0, offset: 0 };
        let dst = GKRAddress::InnerLayer { layer: 1, offset: 0 };
        let relation = NoFieldGKRRelation::CopyInExtensionField { input: src, output: dst };
        let mapping = BTreeMap::new();
        let action = classify_relation(RootId(0), &relation, &mapping).unwrap();
        assert_eq!(action, ForwardAction::CopyAlias { src_addr: src, dst_addr: dst });
    }

    // ── classify_relation: MaxQuadratic in scratch mapping ───────────────────

    #[test]
    fn max_quadratic_in_scratch_yields_skip() {
        let output_addr = GKRAddress::ScratchSpace(7);
        let relation = min_max_quadratic_relation(output_addr);
        let mut mapping = BTreeMap::new();
        mapping.insert(output_addr, 0usize);
        let action = classify_relation(RootId(2), &relation, &mapping).unwrap();
        assert_eq!(action, ForwardAction::SkipScratchPrefill);
    }

    // ── classify_relation: MaxQuadratic NOT in scratch mapping ───────────────

    #[test]
    fn max_quadratic_not_in_scratch_yields_err() {
        let output_addr = GKRAddress::ScratchSpace(99);
        let relation = min_max_quadratic_relation(output_addr);
        let mapping: BTreeMap<GKRAddress, usize> = BTreeMap::new(); // output_addr absent
        let result = classify_relation(RootId(5), &relation, &mapping);
        assert_eq!(result, Err(CompileError::NonScratchMaxQuadratic(RootId(5))));
    }

    // ── build_forward_actions: cache root (no origin) → Compute ─────────────

    #[test]
    fn cache_root_no_origin_yields_compute() {
        let sink_id = cs::gkr_compiler::dag_ir::SinkId(0);
        let mut layer = empty_layer();
        layer.sinks.push(SinkInfo { kind: SinkKind::Cache { layer: 0, offset: 0 }, field: FieldKind::Ext });
        layer.roots.push(Root::Output { expr: cs::gkr_compiler::dag_ir::ExprId(0), sink: sink_id });
        // origins is empty → cache root

        let artifact_layer = make_artifact_layer(vec![]);
        let mapping = BTreeMap::new();
        let actions = build_forward_actions(&layer, &artifact_layer, &mapping).unwrap();

        assert_eq!(actions.len(), 1);
        assert_eq!(actions[&RootId(0)], ForwardAction::Compute);
    }

    // ── build_forward_actions: claim-bearing CopyInBaseField → CopyAlias ────

    #[test]
    fn claim_root_with_copy_relation_yields_copy_alias() {
        let src = GKRAddress::BaseLayerWitness(0);
        let dst = GKRAddress::BaseLayerWitness(1);
        let relation = NoFieldGKRRelation::CopyInBaseField { input: src, output: dst };
        let artifact_layer = make_artifact_layer(vec![relation]);

        let sink_id = cs::gkr_compiler::dag_ir::SinkId(0);
        let mut layer = empty_layer();
        layer.sinks.push(SinkInfo { kind: SinkKind::Export { slot: 0 }, field: FieldKind::Ext });
        layer.roots.push(Root::Output { expr: cs::gkr_compiler::dag_ir::ExprId(0), sink: sink_id });

        let rid = RootId(0);
        layer.origins.insert(rid, RootOrigin {
            group: RootGroup::Gates,
            relation_index: 0,
            slot: RootSlot::Output(0),
        });

        let mapping = BTreeMap::new();
        let actions = build_forward_actions(&layer, &artifact_layer, &mapping).unwrap();

        assert_eq!(actions.len(), 1);
        assert_eq!(actions[&rid], ForwardAction::CopyAlias { src_addr: src, dst_addr: dst });
    }

    // ── NOTE: build_forward_actions + MaxQuadratic classification exercised on
    //    real artifacts by Task 13 (parity gate fixture). ────────────────────
}
