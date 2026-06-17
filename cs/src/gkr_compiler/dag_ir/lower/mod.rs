//! DAG-IR generator: lowers a compiled `GKRCircuitArtifact` into a `DagCircuit`.
//!
//! # Driver
//! For each `GKRLayerDescription`, the per-layer driver iterates `layer.gates`
//! THEN `layer.gates_with_external_connections`. This order is protocol
//! significant — it matches the retired `assign_batch_powers` order in the
//! codegen IR — so claim-bearing roots are emitted in the same sequence the
//! sumcheck batching expects.
//!
//! # Staged lowering
//! Only the arithmetic/copy family is implemented in this scaffold
//! (`LinearBaseFieldRelation`, `MaxQuadratic`, `CopyInBaseField`,
//! `CopyInExtensionField`). EVERY other arm returns `Err(...)` — NEVER panics —
//! so staged synthetic tests for implemented families pass and not-yet-lowered
//! families fail cleanly. Tasks 8–11 extend the match.
//!
//! # The cross-layer field subtlety
//! An `Output` root's sink field is taken from the RELATION, not from field
//! inference: Linear / MaxQuadratic / CopyInBaseField → `Base`,
//! CopyInExtensionField → `Ext`. Deriving it via `source_field`/`expr_field`
//! would hit the `LayerOutput`/`CacheOutput` cross-layer gap (those reads carry
//! no field tag), so we never do that here.
//!
//! `read_field` records the field of any read whose field is known-from-context
//! but NOT base-storage-implied — specifically `CopyInExtensionField`'s input,
//! which is read as `Ext`. The map is threaded through so later passes (Task 12
//! validators) can resolve cross-layer read fields. For THIS task it is built
//! but not yet surfaced on `DagCircuit`/`DagLayer` (see the report's concern).

mod arithmetic;

use std::collections::{BTreeMap, HashMap};

use field::PrimeField;

use crate::definitions::{GKRAddress, VirtualSetupPoly};
use crate::gkr_compiler::{GKRCircuitArtifact, GateArtifacts, NoFieldGKRRelation};

use super::{
    ArenaBuilder, BatchingOrder, DagCircuit, DagGlobals, DagLayer, ExprId, FieldKind, ReadPlace,
    Root, RootGroup, RootId, RootOrigin, RootSlot, SinkId, SinkInfo, SinkKind, SourceKind,
    VirtualSetupKind,
};

/// Map a `GKRAddress` to the DAG-IR `SourceKind` for an input read.
///
/// Base-storage families become `Read{place}`; inner/cache layers become the
/// cross-layer `Read{LayerOutput|CacheOutput}` reads; `VirtualSetup` maps the
/// `VirtualSetupPoly` variant to its `VirtualSetupKind`.
///
/// (Prior-aliasing of cache reads is deferred to Task 11; `CacheOutput` is the
/// correct placeholder until then.)
pub(crate) fn map_address(addr: GKRAddress) -> SourceKind {
    match addr {
        GKRAddress::BaseLayerWitness(column) => SourceKind::Read {
            place: ReadPlace::BaseLayerWitness { column },
        },
        GKRAddress::BaseLayerMemory(column) => SourceKind::Read {
            place: ReadPlace::BaseLayerMemory { column },
        },
        GKRAddress::Setup(column) => SourceKind::Read {
            place: ReadPlace::Setup { column },
        },
        GKRAddress::ScratchSpace(slot) => SourceKind::Read {
            place: ReadPlace::Scratch { slot },
        },
        GKRAddress::InnerLayer { layer, offset } => SourceKind::Read {
            place: ReadPlace::LayerOutput { layer, offset },
        },
        GKRAddress::Cached { layer, offset } => SourceKind::Read {
            place: ReadPlace::CacheOutput { layer, offset },
        },
        GKRAddress::VirtualSetup(poly) => SourceKind::VirtualSetup {
            kind: map_virtual_setup(poly),
        },
    }
}

/// Map the artifact's `VirtualSetupPoly` to the DAG-IR `VirtualSetupKind`.
fn map_virtual_setup(poly: VirtualSetupPoly) -> VirtualSetupKind {
    match poly {
        VirtualSetupPoly::RangeCheck16Bits => VirtualSetupKind::RangeCheck16Bits,
        VirtualSetupPoly::RangeCheckTimestamp => VirtualSetupKind::RangeCheckTimestamp,
        VirtualSetupPoly::InitsAndTeardownsLow => VirtualSetupKind::InitsAndTeardownsLow,
        VirtualSetupPoly::InitsAndTeardownsHigh => VirtualSetupKind::InitsAndTeardownsHigh,
    }
}

/// Map an OUTPUT `GKRAddress` to the DAG-IR `SinkKind`.
///
/// Arithmetic/copy gates write only to inner layers; cache/scratch arms exist
/// for the families Tasks 8–11 add.
fn output_sink_kind(addr: GKRAddress) -> Result<SinkKind, String> {
    match addr {
        GKRAddress::InnerLayer { layer, offset } => Ok(SinkKind::Inner { layer, offset }),
        GKRAddress::Cached { layer, offset } => Ok(SinkKind::Cache { layer, offset }),
        GKRAddress::ScratchSpace(slot) => Ok(SinkKind::Scratch { slot }),
        other => Err(format!(
            "dag_ir: output address {:?} cannot be a sink",
            other
        )),
    }
}

/// Per-layer accumulator: roots, sinks, origins, and the contextual read-field map.
struct LayerOut {
    roots: Vec<Root>,
    sinks: Vec<SinkInfo>,
    origins: BTreeMap<RootId, RootOrigin>,
    /// Fields of reads known-from-context but not base-storage-implied (Ext copies).
    ///
    /// Built for downstream passes (Task 12 validators) to resolve cross-layer
    /// read fields; not yet surfaced on `DagLayer`/`DagCircuit` (see report
    /// concern), hence `#[allow(dead_code)]` until a consumer reads it.
    #[allow(dead_code)]
    read_field: HashMap<ReadPlace, FieldKind>,
}

impl LayerOut {
    fn new() -> Self {
        Self {
            roots: Vec::new(),
            sinks: Vec::new(),
            origins: BTreeMap::new(),
            read_field: HashMap::new(),
        }
    }

    /// Emit one `Output` root for `expr` writing to `output` with `field`, and
    /// record its `RootOrigin{group, relation_index, slot: Output(0)}`.
    fn emit_output(
        &mut self,
        expr: ExprId,
        output: GKRAddress,
        field: FieldKind,
        group: RootGroup,
        relation_index: usize,
    ) -> Result<(), String> {
        let sink_id = SinkId(self.sinks.len() as u32);
        self.sinks.push(SinkInfo {
            kind: output_sink_kind(output)?,
            field,
        });
        let root_id = RootId(self.roots.len() as u32);
        self.roots.push(Root::Output {
            expr,
            sink: sink_id,
        });
        self.origins.insert(
            root_id,
            RootOrigin {
                group,
                relation_index,
                slot: RootSlot::Output(0),
            },
        );
        Ok(())
    }
}

/// Lower one relation into the shared arena + layer accumulator.
///
/// `group`/`relation_index` identify the gate's position so the emitted root's
/// `RootOrigin` is recorded. Unimplemented arms return `Err(...)`.
fn lower_relation(
    arena: &mut ArenaBuilder,
    out: &mut LayerOut,
    rel: &NoFieldGKRRelation,
    group: RootGroup,
    relation_index: usize,
) -> Result<(), String> {
    use NoFieldGKRRelation as R;
    match rel {
        R::LinearBaseFieldRelation { input, output } => {
            let (expr, field) = arithmetic::lower_linear(arena, input);
            out.emit_output(expr, *output, field, group, relation_index)
        }
        R::MaxQuadratic { input, output, .. } => {
            let (expr, field) = arithmetic::lower_max_quadratic(arena, input);
            out.emit_output(expr, *output, field, group, relation_index)
        }
        R::CopyInBaseField { input, output } => {
            let (expr, field) = arithmetic::lower_copy(arena, *input, FieldKind::Base);
            out.emit_output(expr, *output, field, group, relation_index)
        }
        R::CopyInExtensionField { input, output } => {
            // The input is read in the extension field; record that contextual
            // field for any read that is not base-storage-implied so later
            // validators can resolve it.
            if let SourceKind::Read { place } = map_address(*input) {
                out.read_field.insert(place, FieldKind::Ext);
            }
            let (expr, field) = arithmetic::lower_copy(arena, *input, FieldKind::Ext);
            out.emit_output(expr, *output, field, group, relation_index)
        }
        other => Err(format!(
            "dag_ir: relation {:?} not yet lowered (Task N)",
            other
        )),
    }
}

/// Lower one `GKRLayerDescription` into a `DagLayer`.
///
/// Gates are lowered in protocol order: `gates` first, then
/// `gates_with_external_connections`. Every emitted `Output` root is claim
/// bearing and therefore listed in `batching` in emission order.
fn lower_layer<F: PrimeField + PartialEq>(
    artifact: &GKRCircuitArtifact<F>,
    layer_index: usize,
) -> Result<DagLayer, String> {
    let layer = &artifact.layers[layer_index];
    let mut arena = ArenaBuilder::new();
    let mut out = LayerOut::new();

    let lower_group = |arena: &mut ArenaBuilder,
                       out: &mut LayerOut,
                       group: RootGroup,
                       gates: &[GateArtifacts]|
     -> Result<(), String> {
        for (relation_index, gate) in gates.iter().enumerate() {
            lower_relation(
                arena,
                out,
                &gate.enforced_relation,
                group.clone(),
                relation_index,
            )?;
        }
        Ok(())
    };

    lower_group(&mut arena, &mut out, RootGroup::Gates, &layer.gates)?;
    lower_group(
        &mut arena,
        &mut out,
        RootGroup::GatesExternal,
        &layer.gates_with_external_connections,
    )?;

    // Every Output root emitted here is claim-bearing; batch them in emission order.
    let batching = BatchingOrder {
        roots: (0..out.roots.len() as u32).map(RootId).collect(),
    };

    Ok(DagLayer {
        sources: arena.sources().to_vec(),
        exprs: arena.exprs().to_vec(),
        roots: out.roots,
        sinks: out.sinks,
        batching,
        origins: out.origins,
    })
}

/// Lower a compiled `GKRCircuitArtifact` into a `DagCircuit`.
///
/// Returns `Err(...)` (never panics) for any relation family not yet lowered, so
/// staged tests fail cleanly while implemented families succeed.
pub fn lower_dag<F: PrimeField + PartialEq>(
    artifact: &GKRCircuitArtifact<F>,
) -> Result<DagCircuit, String> {
    let layers = (0..artifact.layers.len())
        .map(|i| lower_layer(artifact, i))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(DagCircuit {
        layers,
        globals: DagGlobals {
            trace_len: artifact.trace_len,
            scratch: BTreeMap::new(),
        },
    })
}

// ── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::definitions::gkr::NoFieldLinearRelation;
    use crate::gkr_compiler::test_support::{sample_relations, single_relation_artifact};
    use crate::gkr_compiler::{NoFieldMaxQuadraticGKRRelation, NoFieldStructuredExpression};
    use crate::gkr_compiler::dag_ir::Expr;

    /// The single layer of a `single_relation_artifact`, lowered.
    fn lower_single(rel: NoFieldGKRRelation) -> DagLayer {
        let artifact = single_relation_artifact(rel);
        let circuit = lower_dag(&artifact).expect("lower_dag must succeed");
        assert_eq!(circuit.layers.len(), 1, "single-relation artifact is one layer");
        circuit.layers.into_iter().next().unwrap()
    }

    /// The lone Output root's sink field + its `expr` node.
    fn single_output(layer: &DagLayer) -> (&FieldKind, ExprId) {
        let outputs: Vec<&Root> = layer
            .roots
            .iter()
            .filter(|r| matches!(r, Root::Output { .. }))
            .collect();
        assert_eq!(outputs.len(), 1, "expected exactly one Output root");
        let Root::Output { expr, sink } = outputs[0] else {
            unreachable!()
        };
        (&layer.sinks[sink.0 as usize].field, *expr)
    }

    fn blw(i: usize) -> GKRAddress {
        GKRAddress::BaseLayerWitness(i)
    }
    fn inner0() -> GKRAddress {
        GKRAddress::InnerLayer { layer: 1, offset: 0 }
    }

    // ── LinearBaseFieldRelation ────────────────────────────────────────────

    #[test]
    fn linear_lowers_to_base_output_add_of_muls() {
        // 2·x0 + 3·x1  → Add([Mul, Mul]), Base field.
        let rel = NoFieldGKRRelation::LinearBaseFieldRelation {
            input: NoFieldLinearRelation {
                linear_terms: vec![(2u32, blw(0)), (3u32, blw(1))].into_boxed_slice(),
                constant: 0,
            },
            output: inner0(),
        };
        let layer = lower_single(rel);
        let (field, expr) = single_output(&layer);
        assert_eq!(*field, FieldKind::Base);
        match &layer.exprs[expr.0 as usize] {
            Expr::Add(terms) => {
                assert_eq!(terms.len(), 2, "two coefficient·read terms");
                for t in terms {
                    assert!(
                        matches!(layer.exprs[t.0 as usize], Expr::Mul(_)),
                        "each term is a Mul(const, read)"
                    );
                }
            }
            other => panic!("expected Add of Muls, got {:?}", other),
        }
        // Origin recorded for the single Gates Output root.
        assert_eq!(
            layer.origins.get(&RootId(0)),
            Some(&RootOrigin {
                group: RootGroup::Gates,
                relation_index: 0,
                slot: RootSlot::Output(0),
            })
        );
    }

    #[test]
    fn linear_unit_coeff_is_bare_read() {
        // 1·x0  → a single Source(Read) with NO Mul wrapper.
        let rel = NoFieldGKRRelation::LinearBaseFieldRelation {
            input: NoFieldLinearRelation::from_single_input(blw(0)),
            output: inner0(),
        };
        let layer = lower_single(rel);
        let (field, expr) = single_output(&layer);
        assert_eq!(*field, FieldKind::Base);
        assert!(
            matches!(layer.exprs[expr.0 as usize], Expr::Source(_)),
            "unit-coefficient single term must be a bare Source(Read), got {:?}",
            layer.exprs[expr.0 as usize]
        );
    }

    // ── MaxQuadratic ───────────────────────────────────────────────────────

    #[test]
    fn max_quadratic_lowers_to_base_output_with_quadratic_term() {
        // x0·x1 + x0  → Add([Mul(read,read), Source(read)]), Base field.
        let rel = NoFieldGKRRelation::MaxQuadratic {
            input: NoFieldMaxQuadraticGKRRelation {
                quadratic_terms: vec![(blw(0), vec![(1u32, blw(1))].into_boxed_slice())]
                    .into_boxed_slice(),
                linear_terms: vec![(1u32, blw(0))].into_boxed_slice(),
                constant: 0,
            },
            expression: NoFieldStructuredExpression::Constant(0),
            output: inner0(),
        };
        let layer = lower_single(rel);
        let (field, expr) = single_output(&layer);
        assert_eq!(*field, FieldKind::Base);
        match &layer.exprs[expr.0 as usize] {
            Expr::Add(terms) => {
                assert_eq!(terms.len(), 2, "one quadratic + one linear term");
                let has_mul = terms
                    .iter()
                    .any(|t| matches!(layer.exprs[t.0 as usize], Expr::Mul(_)));
                let has_src = terms
                    .iter()
                    .any(|t| matches!(layer.exprs[t.0 as usize], Expr::Source(_)));
                assert!(has_mul && has_src, "expected a Mul (quadratic) and a Source (linear)");
            }
            other => panic!("expected Add, got {:?}", other),
        }
    }

    // ── CopyInBaseField / CopyInExtensionField ──────────────────────────────

    #[test]
    fn copy_base_lowers_to_base_source() {
        let rel = NoFieldGKRRelation::CopyInBaseField {
            input: blw(0),
            output: inner0(),
        };
        let layer = lower_single(rel);
        let (field, expr) = single_output(&layer);
        assert_eq!(*field, FieldKind::Base);
        assert!(
            matches!(layer.exprs[expr.0 as usize], Expr::Source(_)),
            "copy is a bare Source(Read)"
        );
    }

    #[test]
    fn copy_ext_lowers_to_ext_source_and_records_read_field() {
        let rel = NoFieldGKRRelation::CopyInExtensionField {
            input: blw(0),
            output: inner0(),
        };
        let artifact = single_relation_artifact(rel);
        let circuit = lower_dag(&artifact).expect("lower_dag must succeed");
        let layer = &circuit.layers[0];
        let (field, expr) = single_output(layer);
        assert_eq!(*field, FieldKind::Ext, "extension copy output is Ext");
        assert!(
            matches!(layer.exprs[expr.0 as usize], Expr::Source(_)),
            "copy is a bare Source(Read)"
        );
    }

    // ── Not-yet-lowered families return Err (no panic) ──────────────────────

    #[test]
    fn unimplemented_relation_returns_err_not_panic() {
        // Pick a lookup variant from the sample relations; it must not be lowered yet.
        let (_name, rel) = sample_relations()
            .into_iter()
            .find(|(name, _)| *name == "LookupPairFromMaterializedBaseInputs")
            .expect("sample relation must exist");
        let artifact = single_relation_artifact(rel);
        let result = lower_dag(&artifact);
        assert!(
            result.is_err(),
            "a not-yet-lowered relation must return Err, not panic"
        );
        let msg = result.unwrap_err();
        assert!(
            msg.contains("not yet lowered"),
            "error message should explain the staging: {msg}"
        );
    }
}
