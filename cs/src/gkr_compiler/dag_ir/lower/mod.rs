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
//! The arithmetic/copy family (`LinearBaseFieldRelation`, `MaxQuadratic`,
//! `CopyInBaseField`, `CopyInExtensionField`) and the full lookup family (the two
//! single-output materializations plus every two-output num/den pair gate — see
//! [`lookup`]) are implemented. The remaining grand-product / memory-tuple /
//! inits-teardowns / enforce arms still return `Err(...)` — NEVER panic — so
//! staged synthetic tests for implemented families pass and not-yet-lowered
//! families fail cleanly. Tasks 9–11 extend the match.
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
mod lookup;

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

    /// Emit TWO adjacent `Output` roots — num (slot `Output(0)`) then den (slot
    /// `Output(1)`) — for a two-output lookup gate, writing to `output[0]` and
    /// `output[1]` with `field`. The roots are adjacent in emission order so they
    /// receive consecutive batching powers.
    fn emit_output_pair(
        &mut self,
        num: ExprId,
        den: ExprId,
        output: [GKRAddress; 2],
        field: FieldKind,
        group: RootGroup,
        relation_index: usize,
    ) -> Result<(), String> {
        for (slot, (expr, addr)) in [(num, output[0]), (den, output[1])].into_iter().enumerate() {
            let sink_id = SinkId(self.sinks.len() as u32);
            self.sinks.push(SinkInfo {
                kind: output_sink_kind(addr)?,
                field: field.clone(),
            });
            let root_id = RootId(self.roots.len() as u32);
            self.roots.push(Root::Output {
                expr,
                sink: sink_id,
            });
            self.origins.insert(
                root_id,
                RootOrigin {
                    group: group.clone(),
                    relation_index,
                    slot: RootSlot::Output(slot),
                },
            );
        }
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
    minus_one: u32,
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

        // ── Single-output lookup materializations ───────────────────────────
        R::MaterializeSingleLookupInput {
            input,
            output,
            range_check_width,
        } => {
            // single_column_lookup is a base-valued LookupValue.
            let expr = lookup::single_column_lookup(arena, input, *range_check_width);
            out.emit_output(expr, *output, FieldKind::Base, group, relation_index)
        }
        R::MaterializedVectorLookupInput { input, output } => {
            // folded_lookup is extension-valued (alpha powers are challenges).
            let expr = lookup::folded_lookup(arena, input);
            out.emit_output(expr, *output, FieldKind::Ext, group, relation_index)
        }

        // ── Two-output PAIR family: 1/(b+γ) + 1/(d+γ) ───────────────────────
        R::LookupPairFromBaseInputs {
            input,
            output,
            range_check_width,
        } => {
            let b = lookup::single_column_lookup(arena, &input[0], *range_check_width);
            let d = lookup::single_column_lookup(arena, &input[1], *range_check_width);
            let (num, den) = lookup::pair(arena, b, d);
            out.emit_output_pair(num, den, *output, FieldKind::Ext, group, relation_index)
        }
        R::LookupPairFromMaterializedBaseInputs { input, output } => {
            let b = lookup::read(arena, input[0]);
            let d = lookup::read(arena, input[1]);
            let (num, den) = lookup::pair(arena, b, d);
            out.emit_output_pair(num, den, *output, FieldKind::Ext, group, relation_index)
        }
        R::LookupPairFromVectorInputs { input, output } => {
            let b = lookup::folded_lookup(arena, &input[0]);
            let d = lookup::folded_lookup(arena, &input[1]);
            let (num, den) = lookup::pair(arena, b, d);
            out.emit_output_pair(num, den, *output, FieldKind::Ext, group, relation_index)
        }
        R::LookupPairFromMaterializedVectorInputs { input, output }
        | R::LookupPairFromCachedVectorInputs { input, output } => {
            let b = lookup::read(arena, input[0]);
            let d = lookup::read(arena, input[1]);
            let (num, den) = lookup::pair(arena, b, d);
            out.emit_output_pair(num, den, *output, FieldKind::Ext, group, relation_index)
        }

        // ── Two-output LOOKUP-MINUS-SETUP: 1/(b+γ) − c/(d+γ) ────────────────
        R::LookupFromMaterializedBaseInputWithSetup {
            input,
            setup,
            output,
        }
        | R::LookupFromMaterializedVectorInputWithSetup {
            input,
            setup,
            output,
        } => {
            // b = Read(input); c = multiplicity Read(setup[0]); d = setup Read(setup[1]).
            let b = lookup::read(arena, *input);
            let c = lookup::read(arena, setup[0]);
            let d = lookup::read(arena, setup[1]);
            let (num, den) = lookup::minus_multiplicity(arena, b, c, d, minus_one);
            out.emit_output_pair(num, den, *output, FieldKind::Ext, group, relation_index)
        }
        R::LookupFromVectorInputWithSetup {
            input,
            setup,
            output,
        } => {
            // b = folded_lookup(input); c = multiplicity Read(setup.0);
            // d = alpha-folded setup columns.
            let b = lookup::folded_lookup(arena, input);
            let c = lookup::read(arena, setup.0);
            let d = lookup::folded_setup(arena, &setup.1);
            let (num, den) = lookup::minus_multiplicity(arena, b, c, d, minus_one);
            out.emit_output_pair(num, den, *output, FieldKind::Ext, group, relation_index)
        }

        // ── Two-output DENS-AND-SETUP: a/(b+γ) − c/(d+γ) ────────────────────
        R::LookupWithCachedDensAndSetup {
            input,
            setup,
            output,
        } => {
            // a = Read(input[0]); b = Read(input[1]);
            // c = Read(setup[0]); d = Read(setup[1]).
            let a = lookup::read(arena, input[0]);
            let b = lookup::read(arena, input[1]);
            let c = lookup::read(arena, setup[0]);
            let d = lookup::read(arena, setup[1]);
            let (num, den) = lookup::dens_and_setup(arena, a, b, c, d, minus_one);
            out.emit_output_pair(num, den, *output, FieldKind::Ext, group, relation_index)
        }
        R::LookupWithDensAndSetupExpressions {
            input,
            setup,
            output,
        } => {
            // a = Read(input.0) (mask); b = folded_lookup(input.1);
            // c = Read(setup.0) (multiplicity); d = alpha-folded setup columns.
            let a = lookup::read(arena, input.0);
            let b = lookup::folded_lookup(arena, &input.1);
            let c = lookup::read(arena, setup.0);
            let d = lookup::folded_setup(arena, &setup.1);
            let (num, den) = lookup::dens_and_setup(arena, a, b, c, d, minus_one);
            out.emit_output_pair(num, den, *output, FieldKind::Ext, group, relation_index)
        }
        R::LookupWithDensAndCachedSetup {
            input,
            setup,
            output,
        } => {
            // a = Read(input.0) (mask); b = folded_lookup(input.1);
            // c = Read(setup.0) (multiplicity); d = Read(setup.1) (cached setup).
            let a = lookup::read(arena, input.0);
            let b = lookup::folded_lookup(arena, &input.1);
            let c = lookup::read(arena, setup.0);
            let d = lookup::read(arena, setup.1);
            let (num, den) = lookup::dens_and_setup(arena, a, b, c, d, minus_one);
            out.emit_output_pair(num, den, *output, FieldKind::Ext, group, relation_index)
        }

        // ── Two-output UNBALANCED: a/b + 1/(d+γ) ────────────────────────────
        R::LookupUnbalancedPairWithMaterializedBaseInputs {
            input,
            remainder,
            output,
        }
        | R::LookupUnbalancedPairWithMaterializedVectorInputs {
            input,
            remainder,
            output,
        } => {
            // a = Read(input[0]); b = Read(input[1]) (prior pair); d = Read(remainder).
            let a = lookup::read(arena, input[0]);
            let b = lookup::read(arena, input[1]);
            let d = lookup::read(arena, *remainder);
            let (num, den) = lookup::unbalanced(arena, a, b, d);
            out.emit_output_pair(num, den, *output, FieldKind::Ext, group, relation_index)
        }
        R::LookupUnbalancedPairWithVectorInputs {
            input,
            remainder,
            output,
        } => {
            // a = Read(input[0]); b = Read(input[1]) (prior pair);
            // d = folded_lookup(remainder).
            let a = lookup::read(arena, input[0]);
            let b = lookup::read(arena, input[1]);
            let d = lookup::folded_lookup(arena, remainder);
            let (num, den) = lookup::unbalanced(arena, a, b, d);
            out.emit_output_pair(num, den, *output, FieldKind::Ext, group, relation_index)
        }

        // ── Two-output RATIONAL-PAIR aggregate: a/b + c/d ───────────────────
        R::AggregateLookupRationalPair { input, output } => {
            // input[0] = [a_num, b_den]; input[1] = [c_num, d_den].
            let a = lookup::read(arena, input[0][0]);
            let b = lookup::read(arena, input[0][1]);
            let c = lookup::read(arena, input[1][0]);
            let d = lookup::read(arena, input[1][1]);
            let (num, den) = lookup::rational_pair(arena, a, b, c, d);
            out.emit_output_pair(num, den, *output, FieldKind::Ext, group, relation_index)
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

    // Reduced base-field `−1`, used to encode lookup-numerator subtractions as
    // `a + (−1)·b` (there is no `Sub`/`Neg` node).
    let minus_one = F::CHARACTERISTICS - 1;

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
                minus_one,
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
    fn copy_ext_lowers_to_ext_source() {
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
        // Pick a still-unimplemented variant (grand-product family); it must not
        // be lowered yet. All lookup variants are now lowered (Task 8).
        let (_name, rel) = sample_relations()
            .into_iter()
            .find(|(name, _)| *name == "TrivialProduct")
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

    // ── Lookup lowering (Task 8) ────────────────────────────────────────────

    use crate::definitions::gkr::{
        NoFieldSingleColumnLookupRelation, NoFieldVectorLookupRelation,
    };
    use crate::gkr_compiler::dag_ir::{
        ChallengeKey, LookupValueKind, SourceKind,
    };

    /// Trivial single-input linear query `1·x_addr`.
    fn lin(addr: GKRAddress) -> NoFieldLinearRelation {
        NoFieldLinearRelation::from_single_input(addr)
    }

    fn scl(set: usize) -> NoFieldSingleColumnLookupRelation {
        NoFieldSingleColumnLookupRelation {
            input: lin(blw(0)),
            lookup_set_index: set,
        }
    }

    fn vl(set: usize, n_cols: usize) -> NoFieldVectorLookupRelation {
        NoFieldVectorLookupRelation {
            columns: (0..n_cols).map(|i| lin(blw(i))).collect::<Vec<_>>().into_boxed_slice(),
            lookup_set_index: set,
        }
    }

    fn inner1() -> GKRAddress {
        GKRAddress::InnerLayer { layer: 1, offset: 1 }
    }

    /// All `Output` roots' (field, expr), in root order.
    fn outputs(layer: &DagLayer) -> Vec<(FieldKind, ExprId)> {
        layer
            .roots
            .iter()
            .filter_map(|r| match r {
                Root::Output { expr, sink } => {
                    Some((layer.sinks[sink.0 as usize].field.clone(), *expr))
                }
                _ => None,
            })
            .collect()
    }

    /// Every `LookupValue` source's `set_index`, in source order.
    fn lookup_set_indices(layer: &DagLayer) -> Vec<usize> {
        layer
            .sources
            .iter()
            .filter_map(|s| match &s.kind {
                SourceKind::LookupValue { set_index, .. } => Some(*set_index),
                _ => None,
            })
            .collect()
    }

    /// True if any source is a lookup-multiplicative challenge of power `j`.
    fn has_alpha_pow(layer: &DagLayer, j: u32) -> bool {
        use crate::gkr_compiler::dag_ir::ChallengePower;
        layer.sources.iter().any(|s| {
            matches!(&s.kind, SourceKind::Challenge { reference }
                if reference.key == ChallengeKey::LookupMultiplicative
                    && reference.power == ChallengePower::Static(j))
        })
    }

    /// True if any source is the lookup-additive (gamma) challenge.
    fn has_gamma(layer: &DagLayer) -> bool {
        layer.sources.iter().any(|s| {
            matches!(&s.kind, SourceKind::Challenge { reference }
                if reference.key == ChallengeKey::LookupAdditive)
        })
    }

    fn expr<'a>(layer: &'a DagLayer, id: ExprId) -> &'a Expr {
        &layer.exprs[id.0 as usize]
    }

    // -- single-output materializations --

    #[test]
    fn materialize_single_lookup_is_one_base_range_check_output() {
        let rel = NoFieldGKRRelation::MaterializeSingleLookupInput {
            input: scl(3),
            output: inner0(),
            range_check_width: 16,
        };
        let layer = lower_single(rel);
        let outs = outputs(&layer);
        assert_eq!(outs.len(), 1, "MaterializeSingleLookupInput is single-output");
        assert_eq!(outs[0].0, FieldKind::Base, "single-column lookup is Base");
        // The output expr resolves (through CSE) to a RangeCheck16Index LookupValue.
        let kinds: Vec<_> = layer
            .sources
            .iter()
            .filter_map(|s| match &s.kind {
                SourceKind::LookupValue { kind, .. } => Some(kind.clone()),
                _ => None,
            })
            .collect();
        assert!(
            kinds.contains(&LookupValueKind::RangeCheck16Index),
            "width 16 selects RangeCheck16Index, got {kinds:?}"
        );
        assert_eq!(lookup_set_indices(&layer), vec![3], "set_index carried");
    }

    #[test]
    fn materialize_single_lookup_timestamp_width_picks_timestamp_index() {
        let rel = NoFieldGKRRelation::MaterializeSingleLookupInput {
            input: scl(7),
            output: inner0(),
            range_check_width: 19,
        };
        let layer = lower_single(rel);
        let kinds: Vec<_> = layer
            .sources
            .iter()
            .filter_map(|s| match &s.kind {
                SourceKind::LookupValue { kind, .. } => Some(kind.clone()),
                _ => None,
            })
            .collect();
        assert!(
            kinds.contains(&LookupValueKind::TimestampIndex),
            "non-16 width selects TimestampIndex, got {kinds:?}"
        );
        assert_eq!(lookup_set_indices(&layer), vec![7]);
    }

    #[test]
    fn materialized_vector_lookup_is_one_ext_output_folded() {
        // 3 columns → terms for col0 (no alpha), col1·alpha^1, col2·alpha^2.
        let rel = NoFieldGKRRelation::MaterializedVectorLookupInput {
            input: vl(5, 3),
            output: inner0(),
        };
        let layer = lower_single(rel);
        let outs = outputs(&layer);
        assert_eq!(outs.len(), 1, "MaterializedVectorLookupInput is single-output");
        assert_eq!(outs[0].0, FieldKind::Ext, "folded vector lookup is Ext");
        // Top-level expr is an Add of the per-column terms.
        assert!(
            matches!(expr(&layer, outs[0].1), Expr::Add(_)),
            "folded_lookup top-level is an Add"
        );
        // alpha^1 and alpha^2 present; alpha^0 (col 0) carries no factor.
        assert!(has_alpha_pow(&layer, 1) && has_alpha_pow(&layer, 2));
        assert!(!has_alpha_pow(&layer, 0), "column 0 carries no alpha factor");
        // Every emitted LookupValue carries set_index 5 (one per column).
        assert_eq!(lookup_set_indices(&layer), vec![5, 5, 5]);
    }

    // -- two-output families: shared structural checks --

    /// Assert exactly two adjacent Output roots, both Ext, num = Add, den = Mul,
    /// and (if `expect_lookup_set` is `Some(set)`) every LookupValue set_index == set.
    fn assert_two_output_num_add_den_mul(
        layer: &DagLayer,
        expect_lookup_set: Option<usize>,
    ) {
        let outs = outputs(layer);
        assert_eq!(outs.len(), 2, "pair gate emits exactly two Output roots");
        for (f, _) in &outs {
            assert_eq!(*f, FieldKind::Ext, "two-output lookup roots are Ext");
        }
        // Roots are adjacent (ids 0 and 1) with slots Output(0)/Output(1).
        assert_eq!(
            layer.origins.get(&RootId(0)).map(|o| o.slot.clone()),
            Some(RootSlot::Output(0))
        );
        assert_eq!(
            layer.origins.get(&RootId(1)).map(|o| o.slot.clone()),
            Some(RootSlot::Output(1))
        );
        // num is an Add, den is a Mul.
        assert!(
            matches!(expr(layer, outs[0].1), Expr::Add(_)),
            "num is an Add, got {:?}",
            expr(layer, outs[0].1)
        );
        assert!(
            matches!(expr(layer, outs[1].1), Expr::Mul(_)),
            "den is a Mul, got {:?}",
            expr(layer, outs[1].1)
        );
        assert!(has_gamma(layer), "shifted by gamma");
        if let Some(set) = expect_lookup_set {
            for s in lookup_set_indices(layer) {
                assert_eq!(s, set, "all LookupValue.set_index == relation set_index");
            }
        }
    }

    fn two_out() -> [GKRAddress; 2] {
        [inner0(), inner1()]
    }

    #[test]
    fn pair_from_base_inputs() {
        let rel = NoFieldGKRRelation::LookupPairFromBaseInputs {
            input: [scl(2), scl(2)],
            output: two_out(),
            range_check_width: 16,
        };
        let layer = lower_single(rel);
        assert_two_output_num_add_den_mul(&layer, Some(2));
    }

    #[test]
    fn pair_from_materialized_base_inputs() {
        let rel = NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs {
            input: [blw(0), blw(1)],
            output: two_out(),
        };
        let layer = lower_single(rel);
        // No inline LookupValue (operands are materialized Reads), so no set_index.
        assert_two_output_num_add_den_mul(&layer, None);
        assert!(lookup_set_indices(&layer).is_empty());
    }

    #[test]
    fn pair_from_vector_inputs() {
        let rel = NoFieldGKRRelation::LookupPairFromVectorInputs {
            input: [vl(4, 2), vl(4, 2)],
            output: two_out(),
        };
        let layer = lower_single(rel);
        assert_two_output_num_add_den_mul(&layer, Some(4));
    }

    #[test]
    fn pair_from_materialized_vector_inputs() {
        let rel = NoFieldGKRRelation::LookupPairFromMaterializedVectorInputs {
            input: [blw(0), blw(1)],
            output: two_out(),
        };
        let layer = lower_single(rel);
        assert_two_output_num_add_den_mul(&layer, None);
    }

    #[test]
    fn pair_from_cached_vector_inputs() {
        let rel = NoFieldGKRRelation::LookupPairFromCachedVectorInputs {
            input: [GKRAddress::Cached { layer: 0, offset: 0 }, GKRAddress::Cached { layer: 0, offset: 1 }],
            output: two_out(),
        };
        let layer = lower_single(rel);
        assert_two_output_num_add_den_mul(&layer, None);
    }

    #[test]
    fn from_materialized_base_input_with_setup() {
        let rel = NoFieldGKRRelation::LookupFromMaterializedBaseInputWithSetup {
            input: blw(0),
            setup: [blw(1), GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits)],
            output: two_out(),
        };
        let layer = lower_single(rel);
        assert_two_output_num_add_den_mul(&layer, None);
    }

    #[test]
    fn from_materialized_vector_input_with_setup() {
        let rel = NoFieldGKRRelation::LookupFromMaterializedVectorInputWithSetup {
            input: blw(0),
            setup: [blw(1), GKRAddress::Cached { layer: 0, offset: 0 }],
            output: two_out(),
        };
        let layer = lower_single(rel);
        assert_two_output_num_add_den_mul(&layer, None);
    }

    #[test]
    fn from_vector_input_with_setup() {
        let rel = NoFieldGKRRelation::LookupFromVectorInputWithSetup {
            input: vl(8, 2),
            setup: (blw(0), vec![blw(1), blw(2)].into_boxed_slice()),
            output: two_out(),
        };
        let layer = lower_single(rel);
        assert_two_output_num_add_den_mul(&layer, Some(8));
        // setup folded → alpha^1 present (2 setup cols).
        assert!(has_alpha_pow(&layer, 1));
    }

    #[test]
    fn with_cached_dens_and_setup() {
        let rel = NoFieldGKRRelation::LookupWithCachedDensAndSetup {
            input: [blw(0), GKRAddress::Cached { layer: 0, offset: 0 }],
            setup: [blw(1), GKRAddress::Cached { layer: 0, offset: 1 }],
            output: two_out(),
        };
        let layer = lower_single(rel);
        assert_two_output_num_add_den_mul(&layer, None);
    }

    #[test]
    fn with_dens_and_setup_expressions() {
        let rel = NoFieldGKRRelation::LookupWithDensAndSetupExpressions {
            input: (blw(0), vl(6, 2)),
            setup: (blw(1), vec![blw(2), blw(3)].into_boxed_slice()),
            output: two_out(),
        };
        let layer = lower_single(rel);
        assert_two_output_num_add_den_mul(&layer, Some(6));
    }

    #[test]
    fn with_dens_and_cached_setup() {
        let rel = NoFieldGKRRelation::LookupWithDensAndCachedSetup {
            input: (blw(0), vl(9, 2)),
            setup: (blw(1), GKRAddress::Cached { layer: 0, offset: 0 }),
            output: two_out(),
        };
        let layer = lower_single(rel);
        assert_two_output_num_add_den_mul(&layer, Some(9));
    }

    #[test]
    fn unbalanced_pair_with_materialized_base_inputs() {
        let rel = NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedBaseInputs {
            input: [blw(0), blw(1)],
            remainder: blw(2),
            output: two_out(),
        };
        let layer = lower_single(rel);
        assert_two_output_num_add_den_mul(&layer, None);
    }

    #[test]
    fn unbalanced_pair_with_vector_inputs() {
        let rel = NoFieldGKRRelation::LookupUnbalancedPairWithVectorInputs {
            input: [blw(0), blw(1)],
            remainder: vl(11, 2),
            output: two_out(),
        };
        let layer = lower_single(rel);
        assert_two_output_num_add_den_mul(&layer, Some(11));
    }

    #[test]
    fn unbalanced_pair_with_materialized_vector_inputs() {
        let rel = NoFieldGKRRelation::LookupUnbalancedPairWithMaterializedVectorInputs {
            input: [blw(0), blw(1)],
            remainder: blw(2),
            output: two_out(),
        };
        let layer = lower_single(rel);
        assert_two_output_num_add_den_mul(&layer, None);
    }

    #[test]
    fn aggregate_lookup_rational_pair_num_add_den_mul_no_gamma() {
        // a/b + c/d: num = a·d + c·b (Add of Muls), den = b·d (Mul). No gamma.
        let rel = NoFieldGKRRelation::AggregateLookupRationalPair {
            input: [[blw(0), blw(1)], [blw(2), blw(3)]],
            output: two_out(),
        };
        let layer = lower_single(rel);
        let outs = outputs(&layer);
        assert_eq!(outs.len(), 2);
        for (f, _) in &outs {
            assert_eq!(*f, FieldKind::Ext);
        }
        assert!(matches!(expr(&layer, outs[0].1), Expr::Add(_)), "num is Add(a·d, c·b)");
        assert!(matches!(expr(&layer, outs[1].1), Expr::Mul(_)), "den is Mul(b, d)");
        assert!(!has_gamma(&layer), "rational-pair aggregate has no gamma shift");
        // num's Add terms are both Muls.
        if let Expr::Add(terms) = expr(&layer, outs[0].1) {
            assert_eq!(terms.len(), 2);
            for t in terms {
                assert!(matches!(expr(&layer, *t), Expr::Mul(_)), "num terms are products");
            }
        }
    }

    /// Smoke: every lookup variant from `sample_relations` lowers (no Err).
    /// Covers the two single-output lookup materializations plus every two-output
    /// lookup family (names starting with `Lookup`).
    #[test]
    fn all_lookup_variants_lower_without_err() {
        for (name, rel) in sample_relations() {
            let is_lookup = name.starts_with("Lookup")
                || name == "MaterializeSingleLookupInput"
                || name == "MaterializedVectorLookupInput";
            if !is_lookup {
                continue;
            }
            let artifact = single_relation_artifact(rel);
            assert!(
                lower_dag(&artifact).is_ok(),
                "{name} must lower without Err"
            );
        }
    }
}
