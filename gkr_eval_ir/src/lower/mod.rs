//! DAG-IR generator: lowers a compiled `GKRCircuitArtifact` into a `DagCircuit`.
//!
//! Cache relations are materialized first so same-layer consumers share their
//! expressions. Claim-bearing gates retain artifact order because that order
//! determines batching powers. Output fields come from the relation; validation
//! resolves field kinds for cross-layer reads from the producing sink.

mod arithmetic;
mod constraint;
mod lookup;
mod memory;
mod util;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::validate::validate;

use field::PrimeField;

use cs::definitions::gkr::DECODER_LOOKUP_FORMAL_SET_INDEX;
use cs::definitions::{GKRAddress, VirtualSetupPoly};
use cs::gkr_compiler::{GKRCacheRelation, GKRCircuitArtifact, GKRRelation, GateArtifacts};

use super::{
    simplify::{simplify_circuit, SIMPLIFY_MODULUS},
    ArenaBuilder, BatchingOrder, DagCircuit, DagLayer, ExprId, FieldKind, RangeWidth, ReadPlace,
    ResolutionStrategy, Root, RootGroup, RootId, RootOrigin, SinkInfo, SinkKind, SourceKind,
    VirtualSetupKind,
};

/// Map an input address to a source. Same-layer cache aliases are resolved first.
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

/// Map an output `GKRAddress` to its sink.
fn output_sink_kind(addr: GKRAddress) -> Result<SinkKind, String> {
    match addr {
        GKRAddress::InnerLayer { layer, offset } => Ok(SinkKind::Inner { layer, offset }),
        GKRAddress::Cached { layer, offset } => Ok(SinkKind::Cache { layer, offset }),
        GKRAddress::ScratchSpace(slot) => Ok(SinkKind::Scratch { slot }),
        other => Err(format!(
            "gkr_eval_ir: output address {:?} cannot be a sink",
            other
        )),
    }
}

/// Per-layer accumulator: roots (each carrying its inlined `materialize` sink
/// and `claim` origin) and resolution hints.
struct LayerOut {
    roots: Vec<Root>,
    resolutions: BTreeMap<ExprId, ResolutionStrategy>,
}

impl LayerOut {
    fn new() -> Self {
        Self {
            roots: Vec::new(),
            resolutions: BTreeMap::new(),
        }
    }

    /// Emit one claim-bearing, materialized root.
    fn emit_output(
        &mut self,
        expr: ExprId,
        output: GKRAddress,
        field: FieldKind,
        group: RootGroup,
        relation_index: usize,
    ) -> Result<(), String> {
        self.roots.push(Root {
            expr,
            materialize: Some(SinkInfo {
                kind: output_sink_kind(output)?,
                field,
            }),
            claim: Some(RootOrigin {
                group,
                relation_index,
            }),
        });
        Ok(())
    }

    fn emit_cache(
        &mut self,
        expr: ExprId,
        addr: GKRAddress,
        field: FieldKind,
    ) -> Result<(), String> {
        let (layer, offset) = match addr {
            GKRAddress::Cached { layer, offset } => (layer, offset),
            other => {
                return Err(format!(
                    "gkr_eval_ir: cache relation keyed by non-cache address {:?}",
                    other
                ));
            }
        };
        self.roots.push(Root {
            expr,
            materialize: Some(SinkInfo {
                kind: SinkKind::Cache { layer, offset },
                field,
            }),
            claim: None,
        });
        Ok(())
    }

    /// Emit adjacent numerator and denominator roots in batching order.
    fn emit_output_pair(
        &mut self,
        num: ExprId,
        den: ExprId,
        output: [GKRAddress; 2],
        field: FieldKind,
        group: RootGroup,
        relation_index: usize,
    ) -> Result<(), String> {
        for (expr, addr) in [(num, output[0]), (den, output[1])] {
            self.roots.push(Root {
                expr,
                materialize: Some(SinkInfo {
                    kind: output_sink_kind(addr)?,
                    field,
                }),
                claim: Some(RootOrigin {
                    group,
                    relation_index,
                }),
            });
        }
        Ok(())
    }

    /// Insert a resolution, erroring if `leaf` is already keyed to a DIFFERENT
    /// strategy (a CSE-identity invariant: identical fold ⇒ identical peek).
    /// Idempotent for an equal re-insert.
    fn insert_resolution(
        &mut self,
        leaf: ExprId,
        strategy: ResolutionStrategy,
    ) -> Result<(), String> {
        if let Some(existing) = self.resolutions.get(&leaf) {
            if existing != &strategy {
                return Err(format!(
                    "gkr_eval_ir: resolution CSE collision at {:?}: {:?} vs {:?}",
                    leaf, existing, strategy
                ));
            }
            return Ok(());
        }
        self.resolutions.insert(leaf, strategy);
        Ok(())
    }

    /// Record a single-column lookup leaf's forward-peek strategy.
    /// `range_check_width == 16` selects the rc16 mapping; anything else is timestamp.
    fn record_single(
        &mut self,
        leaf: ExprId,
        set_index: usize,
        range_check_width: u32,
    ) -> Result<(), String> {
        let width = if range_check_width == 16 {
            RangeWidth::Bits16
        } else {
            RangeWidth::Timestamp
        };
        self.insert_resolution(
            leaf,
            ResolutionStrategy::PeekSingleColumn { set_index, width },
        )
    }

    /// Record a generic-vector / decoder lookup leaf's forward-peek strategy.
    /// `set_index == DECODER_LOOKUP_FORMAL_SET_INDEX` ⇒ decoder (needs the predicate).
    /// `num_columns == 0` is a degenerate fold (a `Constant(0)` leaf) — no peek.
    fn record_vector(
        &mut self,
        leaf: ExprId,
        set_index: usize,
        num_columns: usize,
        decoder_predicate: Option<&ReadPlace>,
    ) -> Result<(), String> {
        if num_columns == 0 {
            return Ok(());
        }
        let strategy = if set_index == DECODER_LOOKUP_FORMAL_SET_INDEX {
            let predicate = decoder_predicate.ok_or_else(|| {
                "gkr_eval_ir: decoder lookup fold but circuit has no machine_state predicate"
                    .to_string()
            })?;
            ResolutionStrategy::PeekDecoder {
                predicate: *predicate,
            }
        } else {
            ResolutionStrategy::PeekAggregate { set_index }
        };
        self.insert_resolution(leaf, strategy)
    }

    /// Record a folded-setup leaf's forward-peek strategy (row-indexed, zero-padded).
    /// `num_columns == 0` is a degenerate fold — no peek.
    fn record_setup(&mut self, leaf: ExprId, num_columns: usize) -> Result<(), String> {
        if num_columns == 0 {
            return Ok(());
        }
        self.insert_resolution(leaf, ResolutionStrategy::PeekSetup)
    }
}

#[derive(Clone, Copy)]
struct RelationInputs<'a> {
    minus_one: u32,
    trace_len: usize,
    inits_word_bits: Option<u32>,
    decoder_predicate: Option<&'a ReadPlace>,
}

/// Lower one relation into the shared arena + layer accumulator.
fn lower_relation<F: PrimeField>(
    arena: &mut ArenaBuilder,
    out: &mut LayerOut,
    rel: &GKRRelation<F>,
    group: RootGroup,
    relation_index: usize,
    inputs: RelationInputs<'_>,
) -> Result<(), String> {
    use GKRRelation as R;
    match rel {
        R::LinearBaseFieldRelation { .. }
        | R::EnforceConstraintsMaxQuadratic { .. }
        | R::InitialGrandProductWithoutCaches { .. }
        | R::UnbalancedGrandProductWithCache { .. }
        | R::MaterializeGrandProductTermExpression { .. }
        | R::MaterializeSingleLookupInput { .. }
        | R::LookupWithDensAndSetupExpressions { .. }
        | R::LookupPairFromBaseInputs { .. }
        | R::LookupPairFromCachedVectorInputs { .. }
        | R::LookupPairFromVectorInputs { .. }
        | R::LookupFromVectorInputWithSetup { .. }
        | R::LookupUnbalancedPairWithVectorInputs { .. } => {
            Err("gkr_eval_ir: unsupported relation in retained GPU circuits".to_string())
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
            // The producing sink determines the field of a cross-layer read.
            let (expr, field) = arithmetic::lower_copy(arena, *input, FieldKind::Ext);
            out.emit_output(expr, *output, field, group, relation_index)
        }

        // ── Single-output lookup materializations ───────────────────────────
        R::MaterializedVectorLookupInput { input, output } => {
            // folded_lookup is extension-valued (alpha powers are challenges).
            let expr = lookup::folded_lookup(arena, input);
            out.record_vector(
                expr,
                input.lookup_set_index,
                input.columns.len(),
                inputs.decoder_predicate,
            )?;
            out.emit_output(expr, *output, FieldKind::Ext, group, relation_index)
        }

        // ── Two-output PAIR family: 1/(b+γ) + 1/(d+γ) ───────────────────────
        R::LookupPairFromMaterializedBaseInputs { input, output } => {
            let b = lookup::read(arena, input[0]);
            let d = lookup::read(arena, input[1]);
            let (num, den) = lookup::pair(arena, b, d);
            out.emit_output_pair(num, den, *output, FieldKind::Ext, group, relation_index)
        }
        R::LookupPairFromMaterializedVectorInputs { input, output } => {
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
            let (num, den) = lookup::minus_multiplicity(arena, b, c, d, inputs.minus_one);
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
            let (num, den) = lookup::dens_and_setup(arena, a, b, c, d, inputs.minus_one);
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

        // ── Grand-product / product / mask family (all single Ext output) ───
        R::InitialGrandProductFromCaches { input, output } => {
            // read(a) · read(b) over prior (Ext) cache/inner reads.
            let expr = memory::product_of_reads(arena, input[0], input[1]);
            out.emit_output(expr, *output, FieldKind::Ext, group, relation_index)
        }
        R::TrivialProduct { input, output } => {
            // read(a) · read(b).
            let expr = memory::product_of_reads(arena, input[0], input[1]);
            out.emit_output(expr, *output, FieldKind::Ext, group, relation_index)
        }
        R::MaskIntoIdentityProduct {
            input,
            mask,
            output,
        } => {
            // 1 + mask·(input − 1)   (= input·mask + (1 − mask)).
            let expr = memory::mask_into_identity(arena, *input, *mask, inputs.minus_one);
            out.emit_output(expr, *output, FieldKind::Ext, group, relation_index)
        }

        // ── Inits / teardowns: product of two RAM tuples (single Ext output) ─
        R::InitsOrTeardownsInitialPair {
            timestamp_and_value,
            setup: _,
            output,
            set_idxes,
        } => {
            // The setup [InitsAndTeardownsLow, InitsAndTeardownsHigh] are encoded
            // as VirtualSetup sources inside the tuple builder, matching the
            // companion "Inits And Teardowns".
            let expr = memory::lower_inits_or_teardowns(
                arena,
                timestamp_and_value,
                *set_idxes,
                inputs.trace_len,
                inputs.inits_word_bits,
            );
            out.emit_output(expr, *output, FieldKind::Ext, group, relation_index)
        }

        // ── Enforce / constraint family ─────────────────────────────────────
        R::EnforceSingleMaxQuadraticConstraint { input, .. } => {
            constraint::lower_single_constraint(arena, out, input, group, relation_index);
            Ok(())
        }
    }
}

/// Materialize one cache relation into a `Cache`-sink `Output` root.
///
/// The expr is built by reusing the matching gate builder per
/// [`GKRCacheRelation`] variant (the same arithmetic the codegen IR's
/// `lower_cache` used), and the sink field follows the cache VALUE:
///
/// - `SingleColumnLookup` → [`lookup::single_column_lookup`], `Base` (a base
///   lincomb resolved to a single base lookup column).
/// - `VectorizedLookup` → [`lookup::folded_lookup`], `Ext` (alpha-folded).
/// - `VectorizedLookupSetup` → [`lookup::folded_setup`], `Ext` (alpha-folded
///   setup reads).
/// - `MemoryTuple` → [`memory::lower_memory_tuple`], `Ext` (challenge-folded).
///
fn lower_cache<F: PrimeField>(
    arena: &mut ArenaBuilder,
    out: &mut LayerOut,
    addr: GKRAddress,
    rel: &GKRCacheRelation<F>,
    minus_one: u32,
    decoder_predicate: Option<&ReadPlace>,
) -> Result<ExprId, String> {
    use GKRCacheRelation as C;
    let (expr, field) = match rel {
        C::SingleColumnLookup {
            relation,
            range_check_width,
        } => {
            let expr = lookup::single_column_lookup(arena, relation, *range_check_width as u32);
            out.record_single(expr, relation.lookup_set_index, *range_check_width as u32)?;
            (expr, FieldKind::Base)
        }
        C::VectorizedLookup(vl) => {
            let expr = lookup::folded_lookup(arena, vl);
            out.record_vector(
                expr,
                vl.lookup_set_index,
                vl.columns.len(),
                decoder_predicate,
            )?;
            (expr, FieldKind::Ext)
        }
        C::VectorizedLookupSetup(cols) => {
            let expr = lookup::folded_setup(arena, cols);
            out.record_setup(expr, cols.len())?;
            (expr, FieldKind::Ext)
        }
        C::MemoryTuple(mt) => (
            memory::lower_memory_tuple(arena, mt, minus_one)?,
            FieldKind::Ext,
        ),
    };
    out.emit_cache(expr, addr, field)?;
    Ok(expr)
}

/// Every decoder-lookup consumer must use the global `machine_state.execute` as
/// its mask. `expected_mask == None` ⇒ the circuit has no machine state, so ANY
/// decoder consumer is an error. Inline consumers carry the decoder fold in
/// `input.1` (mask = `input.0`); the cached consumer reads a decoder
/// `VectorizedLookup` cache leaf via `input[1]` (mask = `input[0]`).
fn check_decoder_masks<'a, F: PrimeField + 'a>(
    relations: impl Iterator<Item = &'a GKRRelation<F>>,
    cached_relations: &BTreeMap<GKRAddress, GKRCacheRelation<F>>,
    expected_mask: Option<GKRAddress>,
) -> Result<(), String> {
    use GKRCacheRelation as C;
    use GKRRelation as R;
    let assert_mask = |mask: GKRAddress| -> Result<(), String> {
        match expected_mask {
            Some(exp) if exp == mask => Ok(()),
            Some(exp) => Err(format!(
                "gkr_eval_ir: decoder mask {:?} != machine_state.execute {:?}",
                mask, exp
            )),
            None => Err(format!(
                "gkr_eval_ir: decoder consumer with mask {:?} but no machine_state",
                mask
            )),
        }
    };
    for rel in relations {
        if let R::LookupWithCachedDensAndSetup { input, .. } = rel {
            if let Some(C::VectorizedLookup(vl)) = cached_relations.get(&input[1]) {
                if vl.lookup_set_index == DECODER_LOOKUP_FORMAL_SET_INDEX {
                    assert_mask(input[0])?;
                }
            }
        }
    }
    Ok(())
}

/// Lower one `GKRLayerDescription` into a `DagLayer`.
///
/// Caches are materialized FIRST (so same-layer cache reads resolve to the
/// materialized value's shared `ExprId`), then gates in protocol order: `gates` first, then
/// `gates_with_external_connections`. Every emitted gate `Output`/`Constraint`
/// root is claim bearing and therefore listed in `batching` in emission order;
/// the materialization-only cache roots are excluded.
fn lower_layer<F: PrimeField + PartialEq>(
    artifact: &GKRCircuitArtifact<F>,
    layer_index: usize,
) -> Result<DagLayer, String> {
    let layer = &artifact.layers[layer_index];
    let mut arena = ArenaBuilder::new();
    let mut out = LayerOut::new();

    // Reduced base-field `−1`, used to encode subtractions as `a + (−1)·b` (there
    // is no `Sub`/`Neg` node) — lookup numerators, `IsRegister`, and the mask gate.
    let minus_one = F::CHARACTERISTICS_U32 - 1;

    // Circuit globals the inits/teardowns top-bits constant resolves from.
    let trace_len = artifact.trace_len;
    let inits_word_bits = artifact.memory_layout.inits_and_teardowns_word_bits;

    // Decoder predicate is absent when the circuit has no machine state.
    let decoder_predicate: Option<ReadPlace> = artifact
        .memory_layout
        .machine_state
        .as_ref()
        .map(|t| ReadPlace::BaseLayerMemory { column: t.execute });
    let relation_inputs = RelationInputs {
        minus_one,
        trace_len,
        inits_word_bits,
        decoder_predicate: decoder_predicate.as_ref(),
    };

    let expected_decoder_mask: Option<GKRAddress> = artifact
        .memory_layout
        .machine_state
        .as_ref()
        .map(|t| GKRAddress::BaseLayerMemory(t.execute));
    check_decoder_masks(
        layer
            .gates
            .iter()
            .chain(layer.gates_with_external_connections.iter())
            .map(|g| &g.enforced_relation),
        &layer.cached_relations,
        expected_decoder_mask,
    )?;

    // ── Materialize caches FIRST ─────────────────────────────────────────────
    // Cache roots occupy the leading RootId slots so the cache-address →
    // shared-`ExprId` alias map is populated before any gate is lowered. They are
    // materialization-only (`materialize: Some(Cache)`, `claim: None`): excluded
    // from batching by the `claim.is_some()` filter below.
    let mut cache_aliases: HashMap<GKRAddress, ExprId> = HashMap::new();
    for (addr, rel) in layer.cached_relations.iter() {
        let expr = lower_cache(
            &mut arena,
            &mut out,
            *addr,
            rel,
            minus_one,
            decoder_predicate.as_ref(),
        )?;
        cache_aliases.insert(*addr, expr);
    }
    // From here on, a same-layer cache read IS the materialized value's ExprId.
    arena.set_cache_aliases(cache_aliases);

    let lower_group = |arena: &mut ArenaBuilder,
                       out: &mut LayerOut,
                       group: RootGroup,
                       gates: &[GateArtifacts<F>]|
     -> Result<(), String> {
        for (relation_index, gate) in gates.iter().enumerate() {
            lower_relation(
                arena,
                out,
                &gate.enforced_relation,
                group,
                relation_index,
                relation_inputs,
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

    // Batching order = the claim-bearing roots only (`claim: Some`), in emission
    // order (caches, then gates → gates_external). Cache roots carry `claim: None`
    // and consume no batching power, so they are filtered out here.
    let batching = BatchingOrder {
        roots: out
            .roots
            .iter()
            .enumerate()
            .filter(|(_, r)| r.claim.is_some())
            .map(|(i, _)| RootId(i as u32))
            .collect(),
    };

    Ok(DagLayer {
        sources: arena.sources().to_vec(),
        exprs: arena.exprs().to_vec(),
        roots: out.roots,
        batching,
        resolutions: out.resolutions,
        forward_skip_roots: BTreeSet::new(),
    })
}

fn forward_skip_roots<F: PrimeField>(
    artifact: &GKRCircuitArtifact<F>,
    layer_index: usize,
    layer: &DagLayer,
) -> Result<BTreeSet<RootId>, String> {
    let artifact_layer = &artifact.layers[layer_index];
    let mut skip_roots = BTreeSet::new();
    for (index, root) in layer.roots.iter().enumerate() {
        let Some(claim) = &root.claim else { continue };
        let gates = match claim.group {
            RootGroup::Gates => &artifact_layer.gates,
            RootGroup::GatesExternal => &artifact_layer.gates_with_external_connections,
        };
        let relation = &gates[claim.relation_index].enforced_relation;
        let skip = match relation {
            GKRRelation::MaxQuadratic { output, .. }
                if artifact.scratch_space_mapping.contains_key(output) =>
            {
                true
            }
            GKRRelation::CopyInBaseField { input, .. }
            | GKRRelation::CopyInExtensionField { input, .. } => match map_address(*input) {
                SourceKind::Read { .. } => true,
                other => {
                    return Err(format!(
                        "gkr_eval_ir: copy root {index} has no readable source: {other:?}"
                    ));
                }
            },
            _ => false,
        };
        if skip {
            skip_roots.insert(RootId(index as u32));
        }
    }
    Ok(skip_roots)
}

/// Lower a compiled `GKRCircuitArtifact` into a `DagCircuit`.
///
/// Returns an error for unsupported relation families.
///
/// Each layer is lowered over an unflattened arena, then the circuit is
/// simplified to a fixpoint.
pub fn lower_dag<F: PrimeField + PartialEq>(
    artifact: &GKRCircuitArtifact<F>,
) -> Result<DagCircuit, String> {
    if F::CHARACTERISTICS_U32 as u64 != SIMPLIFY_MODULUS {
        return Err(format!(
            "gkr_eval_ir: simplification requires modulus {SIMPLIFY_MODULUS} (BabyBear), \
             but the field characteristic is {}",
            F::CHARACTERISTICS_U32
        ));
    }
    let mut layers = (0..artifact.layers.len())
        .map(|i| lower_layer(artifact, i))
        .collect::<Result<Vec<_>, _>>()?;
    for (index, layer) in layers.iter_mut().enumerate() {
        layer.forward_skip_roots = forward_skip_roots(artifact, index, layer)?;
    }

    let dag = simplify_circuit(DagCircuit { layers });
    validate(&dag)?;
    Ok(dag)
}
