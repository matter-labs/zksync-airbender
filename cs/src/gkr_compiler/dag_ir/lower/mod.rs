//! DAG-IR generator: lowers a compiled `GKRCircuitArtifact` into a `DagCircuit`.
//!
//! # Driver
//! For each `GKRLayerDescription`, the per-layer driver first materializes
//! `layer.cached_relations` into `Cache`-sink `Output` roots, then iterates
//! `layer.gates` THEN `layer.gates_with_external_connections`. The gate order is
//! protocol significant — it matches the retired `assign_batch_powers` order in
//! the codegen IR — so claim-bearing roots are emitted in the same sequence the
//! sumcheck batching expects.
//!
//! # Caches (materialization-only roots)
//! Each `(addr, NoFieldGKRCacheRelation)` lowers via [`lower_cache`] to a
//! `Cache{layer,offset}`-sink `Output` root using the same per-variant builder a
//! gate would use (single-column lookup → `Base`; vectorized lookup / vectorized
//! setup / memory tuple → `Ext`). Cache roots are NOT claim-bearing: they record
//! no `RootOrigin` and are excluded from the `BatchingOrder` (they consume no
//! batching power), matching the source artifact where caches are computed per
//! layer but excluded from batch-power assignment. Caches are materialized FIRST
//! so the cache-address → shared-`ExprId` alias map is populated; a subsequent
//! gate input that reads a same-layer cache address then resolves directly to
//! that value's shared `ExprId` (in-layer reuse = DAG sharing) instead of a
//! `Read(CacheOutput)` compatibility read — see [`util::read_expr`]. A genuine
//! external/compat cache read (no in-layer materializer) still falls back to
//! `Read(CacheOutput)`.
//!
//! # Staged lowering
//! The arithmetic/copy family (`LinearBaseFieldRelation`, `MaxQuadratic`,
//! `CopyInBaseField`, `CopyInExtensionField`), the full lookup family (the two
//! single-output materializations plus every two-output num/den pair gate — see
//! [`lookup`]), the grand-product / memory-tuple / mask / inits-teardowns
//! family (see [`memory`]), and the enforce/constraint family
//! (`EnforceSingleMaxQuadraticConstraint`, `EnforceConstraintsMaxQuadratic` — see
//! [`constraint`]) are implemented. The `NoFieldGKRRelation` match is now
//! exhaustive. The only remaining `Err(...)` path is the confirmed-dead
//! `U32SpaceGeneric` address form inside [`memory::lower_memory_tuple`], which is
//! NEVER panicked on — it returns `Err` (Task 14 audits its absence from golden
//! artifacts).
//!
//! # The cross-layer field subtlety
//! An `Output` root's sink field is taken from the RELATION, not from field
//! inference: Linear / MaxQuadratic / CopyInBaseField → `Base`,
//! CopyInExtensionField → `Ext`. Deriving it via `source_field`/`expr_field`
//! would hit the `LayerOutput`/`CacheOutput` cross-layer gap (those reads carry
//! no field tag), so we never do that here. Cross-layer read fields are resolved
//! by the Task-12 validator, which walks layers in declaration order and reads a
//! later layer's `Read{LayerOutput|CacheOutput}` field from the producing layer's
//! sink `FieldKind` — so the generator records no per-read field map of its own.

mod arithmetic;
mod constraint;
mod lookup;
mod memory;
mod util;

use std::collections::{BTreeMap, HashMap};

use field::PrimeField;

use crate::definitions::{GKRAddress, VirtualSetupPoly};
use crate::definitions::gkr::DECODER_LOOKUP_FORMAL_SET_INDEX;
use crate::gkr_compiler::{
    GKRCircuitArtifact, GateArtifacts, NoFieldGKRCacheRelation, NoFieldGKRRelation,
};

use super::{
    simplify::SIMPLIFY_MODULUS, simplify_circuit, ArenaBuilder, BatchingOrder, ClaimInfo,
    DagCircuit, DagGlobals, DagLayer, ExprId, FieldKind, FillSource, RangeWidth, ReadPlace,
    ResolutionStrategy, Root, RootGroup, RootId, RootOrigin, RootSlot, SinkInfo, SinkKind,
    SourceKind, VirtualSetupKind,
};

/// Which arena/pass pipeline `lower_layer` should use.
///
/// `Simplified` (the production path via [`lower_dag`]) builds an unflattened
/// arena (`ArenaBuilder::with_flatten(false)`) so `simplify_circuit`'s
/// fan-out-aware rewrites see the real DAG shape; `lower_dag` runs the
/// simplify pass once all layers are lowered. `Legacy` (via
/// [`lower_dag_legacy`], test-support only) reconstructs the pre-simplification
/// pipeline: build-time flattening on, no simplify pass — used for
/// differential gates that need the un-simplified reference shape (spec
/// G-diff-b).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum LowerMode {
    Simplified,
    Legacy,
}

/// Map a `GKRAddress` to the DAG-IR `SourceKind` for an input read.
///
/// Base-storage families become `Read{place}`; inner/cache layers become the
/// cross-layer `Read{LayerOutput|CacheOutput}` reads; `VirtualSetup` maps the
/// `VirtualSetupPoly` variant to its `VirtualSetupKind`.
///
/// This is the field-agnostic fallback. A `GKRAddress::Cached` materialized as a
/// cache value in the current layer resolves to that value's shared `ExprId`
/// BEFORE this fallback runs (see [`util::read_expr`]); the `CacheOutput` arm
/// here is the genuine external/compat read for caches with no in-layer
/// materializer.
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

    /// Emit one claim-bearing `Output` root for `expr` writing to `output` with
    /// `field`. Sink inlined into `materialize`; origin into
    /// `claim` (`RootOrigin{group, relation_index, slot: Output(0)}`).
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
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group,
                    relation_index,
                    slot: RootSlot::Output(0),
                },
            }),
        });
        Ok(())
    }

    /// Emit one materialization-only cache `Output` root for `expr`, writing to
    /// the `Cache{layer,offset}` sink at `addr` with `field`, and return its
    /// `RootId`.
    ///
    /// Cache roots are NOT claim-bearing: they record NO `RootOrigin` and are NOT
    /// added to the batching order. They materialize the value so it is committed;
    /// same-layer consumers reuse the value by sharing its `ExprId` (DAG sharing),
    /// not by referencing this root (see the module + design docs).
    fn emit_cache(
        &mut self,
        expr: ExprId,
        addr: GKRAddress,
        field: FieldKind,
    ) -> Result<RootId, String> {
        let (layer, offset) = match addr {
            GKRAddress::Cached { layer, offset } => (layer, offset),
            other => {
                return Err(format!(
                    "dag_ir: cache relation keyed by non-cache address {:?}",
                    other
                ));
            }
        };
        let root_id = RootId(self.roots.len() as u32);
        self.roots.push(Root {
            expr,
            materialize: Some(SinkInfo {
                kind: SinkKind::Cache { layer, offset },
                field,
            }),
            claim: None,
        });
        Ok(root_id)
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
            self.roots.push(Root {
                expr,
                materialize: Some(SinkInfo {
                    kind: output_sink_kind(addr)?,
                    field: field.clone(),
                }),
                claim: Some(ClaimInfo {
                    origin: RootOrigin {
                        group: group.clone(),
                        relation_index,
                        slot: RootSlot::Output(slot),
                    },
                }),
            });
        }
        Ok(())
    }

    /// Insert a resolution, erroring if `leaf` is already keyed to a DIFFERENT
    /// strategy (a CSE-identity invariant: identical fold ⇒ identical peek).
    /// Idempotent for an equal re-insert.
    fn insert_resolution(&mut self, leaf: ExprId, strat: ResolutionStrategy) -> Result<(), String> {
        if let Some(existing) = self.resolutions.get(&leaf) {
            if existing != &strat {
                return Err(format!(
                    "dag_ir: resolution CSE collision at {:?}: {:?} vs {:?}",
                    leaf, existing, strat
                ));
            }
            return Ok(());
        }
        self.resolutions.insert(leaf, strat);
        Ok(())
    }

    /// Record a single-column lookup leaf's forward-peek strategy.
    /// `range_check_width == 16` selects the rc16 mapping; anything else is timestamp.
    fn record_single(&mut self, leaf: ExprId, set_index: usize, range_check_width: u32) -> Result<(), String> {
        let width = if range_check_width == 16 {
            RangeWidth::Bits16
        } else {
            RangeWidth::Timestamp
        };
        self.insert_resolution(leaf, ResolutionStrategy::PeekSingleColumn { set_index, width })
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
        // PeekDecoder is only ever emitted for a decoder-set fold that was
        // reached via a masked consumer (LookupWithDensAndSetupExpressions /
        // LookupWithDensAndCachedSetup). The mask is enforced upstream by
        // check_decoder_masks, so an unmasked decoder fold cannot occur on the
        // real pipeline — any decoder consumer that bypasses the mask guard
        // is a generator bug caught before this point.
        let strat = if set_index == DECODER_LOOKUP_FORMAL_SET_INDEX {
            let predicate = decoder_predicate
                .ok_or_else(|| {
                    "dag_ir: decoder lookup fold but circuit has no machine_state predicate".to_string()
                })?
                .clone();
            ResolutionStrategy::PeekDecoder { predicate, fill: FillSource::DecoderLookupFill }
        } else {
            ResolutionStrategy::PeekAggregate { set_index }
        };
        self.insert_resolution(leaf, strat)
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

/// Lower one relation into the shared arena + layer accumulator.
///
/// `group`/`relation_index` identify the gate's position so the emitted root's
/// `RootOrigin` is recorded. `trace_len`/`inits_word_bits` are circuit globals the
/// inits/teardowns top-bits constant needs (see [`memory::lower_inits_or_teardowns`]).
fn lower_relation(
    arena: &mut ArenaBuilder,
    out: &mut LayerOut,
    rel: &NoFieldGKRRelation,
    group: RootGroup,
    relation_index: usize,
    minus_one: u32,
    trace_len: usize,
    inits_word_bits: Option<u32>,
    decoder_predicate: Option<&ReadPlace>,
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
            // The input is read in the extension field. The cross-layer read's
            // `Ext` field is resolved by the Task-12 validator from the producing
            // layer's sink, so nothing is recorded here.
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
            out.record_single(expr, input.lookup_set_index, *range_check_width)?;
            out.emit_output(expr, *output, FieldKind::Base, group, relation_index)
        }
        R::MaterializedVectorLookupInput { input, output } => {
            // folded_lookup is extension-valued (alpha powers are challenges).
            let expr = lookup::folded_lookup(arena, input);
            out.record_vector(expr, input.lookup_set_index, input.columns.len(), decoder_predicate)?;
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
            out.record_single(b, input[0].lookup_set_index, *range_check_width)?;
            out.record_single(d, input[1].lookup_set_index, *range_check_width)?;
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
            out.record_vector(b, input[0].lookup_set_index, input[0].columns.len(), decoder_predicate)?;
            out.record_vector(d, input[1].lookup_set_index, input[1].columns.len(), decoder_predicate)?;
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
            out.record_vector(b, input.lookup_set_index, input.columns.len(), decoder_predicate)?;
            let c = lookup::read(arena, setup.0);
            let d = lookup::folded_setup(arena, &setup.1);
            out.record_setup(d, setup.1.len())?;
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
            out.record_vector(b, input.1.lookup_set_index, input.1.columns.len(), decoder_predicate)?;
            let c = lookup::read(arena, setup.0);
            let d = lookup::folded_setup(arena, &setup.1);
            out.record_setup(d, setup.1.len())?;
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
            out.record_vector(b, input.1.lookup_set_index, input.1.columns.len(), decoder_predicate)?;
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
            out.record_vector(d, remainder.lookup_set_index, remainder.columns.len(), decoder_predicate)?;
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
        R::InitialGrandProductWithoutCaches { input, output } => {
            // lower_memory_tuple(a) · lower_memory_tuple(b).
            let expr = memory::product_of_tuples(arena, &input[0], &input[1], minus_one)?;
            out.emit_output(expr, *output, FieldKind::Ext, group, relation_index)
        }
        R::UnbalancedGrandProductWithCache {
            scalar,
            input,
            output,
        } => {
            // read(scalar) · read(input).
            let expr = memory::product_of_reads(arena, *scalar, *input);
            out.emit_output(expr, *output, FieldKind::Ext, group, relation_index)
        }
        R::TrivialProduct { input, output } => {
            // read(a) · read(b).
            let expr = memory::product_of_reads(arena, input[0], input[1]);
            out.emit_output(expr, *output, FieldKind::Ext, group, relation_index)
        }
        R::MaterializeGrandProductTermExpression { input, output } => {
            // lower_memory_tuple(input).
            let expr = memory::lower_memory_tuple(arena, input, minus_one)?;
            out.emit_output(expr, *output, FieldKind::Ext, group, relation_index)
        }
        R::MaskIntoIdentityProduct {
            input,
            mask,
            output,
        } => {
            // 1 + mask·(input − 1)   (= input·mask + (1 − mask)).
            let expr = memory::mask_into_identity(arena, *input, *mask, minus_one);
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
                trace_len,
                inits_word_bits,
            );
            out.emit_output(expr, *output, FieldKind::Ext, group, relation_index)
        }

        // ── Enforce / constraint family (Task 10) ────────────────────────────
        R::EnforceSingleMaxQuadraticConstraint { input, .. } => {
            constraint::lower_single_constraint(arena, out, input, group, relation_index);
            Ok(())
        }
        R::EnforceConstraintsMaxQuadratic { input } => {
            constraint::lower_batched_constraint(arena, out, input, group, relation_index);
            Ok(())
        }
    }
}

/// Materialize one cache relation into a `Cache`-sink `Output` root.
///
/// The expr is built by reusing the matching gate builder per
/// [`NoFieldGKRCacheRelation`] variant (the same arithmetic the codegen IR's
/// `lower_cache` used), and the sink field follows the cache VALUE:
///
/// - `SingleColumnLookup` → [`lookup::single_column_lookup`], `Base` (a base
///   lincomb resolved to a single base lookup column).
/// - `VectorizedLookup` → [`lookup::folded_lookup`], `Ext` (alpha-folded).
/// - `VectorizedLookupSetup` → [`lookup::folded_setup`], `Ext` (alpha-folded
///   setup reads).
/// - `MemoryTuple` → [`memory::lower_memory_tuple`], `Ext` (challenge-folded).
///
/// Returns the materialized root's `RootId` AND the cache value's `ExprId`. The
/// root is materialization-only: it carries no `RootOrigin` and is excluded from
/// the batching order. The returned `ExprId` is the value's shared expr, which
/// same-layer consumers alias to (in-layer reuse = DAG sharing).
fn lower_cache(
    arena: &mut ArenaBuilder,
    out: &mut LayerOut,
    addr: GKRAddress,
    rel: &NoFieldGKRCacheRelation,
    minus_one: u32,
    decoder_predicate: Option<&ReadPlace>,
) -> Result<(RootId, ExprId), String> {
    use NoFieldGKRCacheRelation as C;
    let (expr, field) = match rel {
        C::SingleColumnLookup {
            relation,
            range_check_width,
        } => {
            let expr =
                lookup::single_column_lookup(arena, relation, *range_check_width as u32);
            out.record_single(expr, relation.lookup_set_index, *range_check_width as u32)?;
            (expr, FieldKind::Base)
        }
        C::VectorizedLookup(vl) => {
            let expr = lookup::folded_lookup(arena, vl);
            out.record_vector(expr, vl.lookup_set_index, vl.columns.len(), decoder_predicate)?;
            (expr, FieldKind::Ext)
        }
        C::VectorizedLookupSetup(cols) => {
            let expr = lookup::folded_setup(arena, cols);
            out.record_setup(expr, cols.len())?;
            (expr, FieldKind::Ext)
        }
        C::MemoryTuple(mt) => (memory::lower_memory_tuple(arena, mt, minus_one)?, FieldKind::Ext),
    };
    let root_id = out.emit_cache(expr, addr, field)?;
    Ok((root_id, expr))
}

/// Every decoder-lookup consumer must use the global `machine_state.execute` as
/// its mask. `expected_mask == None` ⇒ the circuit has no machine state, so ANY
/// decoder consumer is an error. Inline consumers carry the decoder fold in
/// `input.1` (mask = `input.0`); the cached consumer reads a decoder
/// `VectorizedLookup` cache leaf via `input[1]` (mask = `input[0]`).
fn check_decoder_masks<'a>(
    relations: impl Iterator<Item = &'a NoFieldGKRRelation>,
    cached_relations: &BTreeMap<GKRAddress, NoFieldGKRCacheRelation>,
    expected_mask: Option<GKRAddress>,
) -> Result<(), String> {
    use NoFieldGKRCacheRelation as C;
    use NoFieldGKRRelation as R;
    let assert_mask = |mask: GKRAddress| -> Result<(), String> {
        match expected_mask {
            Some(exp) if exp == mask => Ok(()),
            Some(exp) => Err(format!("dag_ir: decoder mask {:?} != machine_state.execute {:?}", mask, exp)),
            None => Err(format!("dag_ir: decoder consumer with mask {:?} but no machine_state", mask)),
        }
    };
    for rel in relations {
        match rel {
            R::LookupWithDensAndSetupExpressions { input, .. }
            | R::LookupWithDensAndCachedSetup { input, .. } => {
                if input.1.lookup_set_index == DECODER_LOOKUP_FORMAL_SET_INDEX {
                    assert_mask(input.0)?;
                }
            }
            R::LookupWithCachedDensAndSetup { input, .. } => {
                if let Some(C::VectorizedLookup(vl)) = cached_relations.get(&input[1]) {
                    if vl.lookup_set_index == DECODER_LOOKUP_FORMAL_SET_INDEX {
                        assert_mask(input[0])?;
                    }
                }
            }
            _ => {}
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
    mode: LowerMode,
) -> Result<DagLayer, String> {
    let layer = &artifact.layers[layer_index];
    let mut arena = match mode {
        // Unflattened: `simplify_circuit` (run once by `lower_dag` after all
        // layers are lowered) is a fan-out-aware rewrite over the real DAG
        // shape, so build-time flattening must be off here.
        LowerMode::Simplified => ArenaBuilder::with_flatten(false),
        // Pre-simplification reference shape: build-time flattening on, matching
        // the pipeline `lower_dag_legacy` reconstructs.
        LowerMode::Legacy => ArenaBuilder::with_flatten(true),
    };
    let mut out = LayerOut::new();

    // Reduced base-field `−1`, used to encode subtractions as `a + (−1)·b` (there
    // is no `Sub`/`Neg` node) — lookup numerators, `IsRegister`, and the mask gate.
    let minus_one = F::CHARACTERISTICS - 1;

    // Circuit globals the inits/teardowns top-bits constant resolves from.
    let trace_len = artifact.trace_len;
    let inits_word_bits = artifact.memory_layout.inits_and_teardowns_word_bits;

    // Decoder predicate is the circuit global `machine_state.execute`. None when the
    // circuit has no machine state (then no decoder lookup exists either). Tasks 3-4 use it.
    // OWNED here; threaded downward as `Option<&ReadPlace>` because `ReadPlace` is
    // `Clone` not `Copy` — passing it by value to many call sites would move it.
    let decoder_predicate: Option<ReadPlace> = artifact
        .memory_layout
        .machine_state
        .as_ref()
        .map(|t| ReadPlace::BaseLayerMemory { column: t.execute });

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
        let (_root_id, expr) =
            lower_cache(&mut arena, &mut out, *addr, rel, minus_one, decoder_predicate.as_ref())?;
        cache_aliases.insert(*addr, expr); // alias → shared ExprId (was: root_id)
    }
    // From here on, a same-layer cache read IS the materialized value's ExprId.
    arena.set_cache_aliases(cache_aliases);

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
                trace_len,
                inits_word_bits,
                decoder_predicate.as_ref(),
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

    // Derived-fence invariant: every arena-fenced node (multi-column fold-leaf
    // `Add`s marked non-flattenable — see `ArenaBuilder::fenced_add`) must be a
    // `resolutions` key, since fencing exists ONLY to keep those leaves
    // single-operand and findable by the resolution-driven forward evaluator.
    // A fenced node with no resolution entry means the derived-fence rule
    // (fence ⟺ resolution key) was violated upstream — surface it as an error,
    // not a silent miscompile.
    for f in arena.fenced() {
        if !out.resolutions.contains_key(f) {
            return Err(format!(
                "dag_ir: fenced node {f:?} has no resolution entry — derived-fence rule violated"
            ));
        }
    }

    Ok(DagLayer {
        sources: arena.sources().to_vec(),
        exprs: arena.exprs().to_vec(),
        roots: out.roots,
        batching,
        resolutions: out.resolutions,
    })
}

/// Lower a compiled `GKRCircuitArtifact` into a `DagCircuit`.
///
/// Returns `Err(...)` (never panics) for any relation family not yet lowered, so
/// staged tests fail cleanly while implemented families succeed.
///
/// Production path: each layer is lowered over an unflattened arena
/// (`LowerMode::Simplified`), then the whole circuit is run once through
/// `simplify_circuit` (a fixpoint, always value-preserving pass — see
/// `simplify.rs`). See [`lower_dag_legacy`] for the pre-simplification
/// reference pipeline kept for differential tests.
pub fn lower_dag<F: PrimeField + PartialEq>(
    artifact: &GKRCircuitArtifact<F>,
) -> Result<DagCircuit, String> {
    if F::CHARACTERISTICS as u64 != SIMPLIFY_MODULUS {
        return Err(format!(
            "dag_ir: simplify pass is hardcoded to modulus {SIMPLIFY_MODULUS} (BabyBear) but \
             field characteristic is {}; dag_ir simplify would silently const-fold mod the wrong prime",
            F::CHARACTERISTICS
        ));
    }
    let layers = (0..artifact.layers.len())
        .map(|i| lower_layer(artifact, i, LowerMode::Simplified))
        .collect::<Result<Vec<_>, _>>()?;

    let dag = DagCircuit {
        layers,
        globals: DagGlobals {
            trace_len: artifact.trace_len,
            scratch: BTreeMap::new(),
        },
    };
    Ok(simplify_circuit(dag))
}

/// Lower a compiled `GKRCircuitArtifact` into a `DagCircuit` via the
/// pre-simplification pipeline: build-time arena flattening ON, and NO
/// `simplify_circuit` pass.
///
/// Test-support only: reconstructs the pre-simplification pipeline for
/// differential gates (spec G-diff-b). Production code must call [`lower_dag`].
pub fn lower_dag_legacy<F: PrimeField + PartialEq>(
    artifact: &GKRCircuitArtifact<F>,
) -> Result<DagCircuit, String> {
    if F::CHARACTERISTICS as u64 != SIMPLIFY_MODULUS {
        return Err(format!(
            "dag_ir: simplify pass is hardcoded to modulus {SIMPLIFY_MODULUS} (BabyBear) but \
             field characteristic is {}; dag_ir simplify would silently const-fold mod the wrong prime",
            F::CHARACTERISTICS
        ));
    }
    let layers = (0..artifact.layers.len())
        .map(|i| lower_layer(artifact, i, LowerMode::Legacy))
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
            .filter(|r| r.materialize.is_some())
            .collect();
        assert_eq!(outputs.len(), 1, "expected exactly one Output root");
        let root = outputs[0];
        (&root.materialize.as_ref().unwrap().field, root.expr)
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
            layer.roots[0].claim.as_ref().map(|c| &c.origin),
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

    // ── Confirmed-dead U32SpaceGeneric address form returns Err (no panic) ──

    #[test]
    fn u32_space_generic_address_returns_err_not_panic() {
        // The only remaining Err path: a memory tuple whose address is the
        // confirmed-dead U32SpaceGeneric form must return Err, never panic.
        use crate::gkr_compiler::{
            CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
            NoFieldSpecialMemoryContributionRelation,
        };
        use crate::definitions::gkr::RamWordRepresentation;
        let generic = NoFieldSpecialMemoryContributionRelation {
            address_space: CompiledAddressSpaceRelationStrict::Constant(0),
            address: CompiledAddressStrict::U32SpaceGeneric([
                (vec![(1u64, 0usize)].into_boxed_slice(), 0u64),
                (vec![(1u64, 1usize)].into_boxed_slice(), 0u64),
            ]),
            timestamp: CompiledMemoryTimestamp::Zero,
            value: RamWordRepresentation::Zero,
            timestamp_offset: 0,
        };
        let rel = NoFieldGKRRelation::MaterializeGrandProductTermExpression {
            input: generic,
            output: inner0(),
        };
        let artifact = single_relation_artifact(rel);
        let result = lower_dag(&artifact);
        assert!(
            result.is_err(),
            "U32SpaceGeneric must return Err, not panic"
        );
        let msg = result.unwrap_err();
        assert!(
            msg.contains("U32SpaceGeneric"),
            "error message should name the dead path: {msg}"
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

    /// All `Output` (materialized) roots' (field, expr), in root order.
    fn outputs(layer: &DagLayer) -> Vec<(FieldKind, ExprId)> {
        layer
            .roots
            .iter()
            .filter_map(|r| r.materialize.as_ref().map(|s| (s.field, r.expr)))
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
            layer.roots[0].claim.as_ref().map(|c| c.origin.slot.clone()),
            Some(RootSlot::Output(0))
        );
        assert_eq!(
            layer.roots[1].claim.as_ref().map(|c| c.origin.slot.clone()),
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

    // ── Memory / grand-product / mask / inits-teardowns lowering (Task 9) ────

    use crate::definitions::gkr::RamWordRepresentation;
    use crate::definitions::VirtualSetupPoly;
    use crate::gkr_compiler::dag_ir::{ChallengePower, PermutationSlot};
    use crate::gkr_compiler::test_support::sample_relation_cases;
    use crate::gkr_compiler::{
        CompiledAddressSpaceRelationStrict, CompiledAddressStrict, CompiledMemoryTimestamp,
        InitsOrTeardownsTimestampAndValue, NoFieldSpecialMemoryContributionRelation,
    };

    fn blm(i: usize) -> GKRAddress {
        GKRAddress::BaseLayerMemory(i)
    }

    /// True if any source is the additive permutation challenge (`beta_perm`).
    fn has_permutation_additive(layer: &DagLayer) -> bool {
        layer.sources.iter().any(|s| {
            matches!(&s.kind, SourceKind::Challenge { reference }
                if reference.key == ChallengeKey::PermutationAdditive)
        })
    }

    /// True if a permutation-linearization challenge for `slot` is present.
    fn has_perm_slot(layer: &DagLayer, slot: PermutationSlot) -> bool {
        layer.sources.iter().any(|s| {
            matches!(&s.kind, SourceKind::Challenge { reference }
                if reference.key == ChallengeKey::PermutationLinearization(slot.clone())
                    && reference.power == ChallengePower::One)
        })
    }

    /// `set` of every `BaseLayerMemory` column read in the layer.
    fn memory_reads(layer: &DagLayer) -> std::collections::BTreeSet<usize> {
        layer
            .sources
            .iter()
            .filter_map(|s| match &s.kind {
                SourceKind::Read {
                    place: ReadPlace::BaseLayerMemory { column },
                } => Some(*column),
                _ => None,
            })
            .collect()
    }

    /// True if any `VirtualSetup` source of `kind` is present.
    fn has_virtual_setup(layer: &DagLayer, kind: VirtualSetupKind) -> bool {
        layer.sources.iter().any(|s| {
            matches!(&s.kind, SourceKind::VirtualSetup { kind: k } if *k == kind)
        })
    }

    /// Wrap a memory descriptor in a single-output `MaterializeGrandProductTermExpression`.
    fn materialize_tuple(desc: NoFieldSpecialMemoryContributionRelation) -> NoFieldGKRRelation {
        NoFieldGKRRelation::MaterializeGrandProductTermExpression {
            input: desc,
            output: inner0(),
        }
    }

    // -- grand-product / product arms: single Ext Mul output --

    #[test]
    fn initial_grand_product_from_caches_is_ext_mul() {
        let rel = NoFieldGKRRelation::InitialGrandProductFromCaches {
            input: [
                GKRAddress::Cached { layer: 0, offset: 0 },
                GKRAddress::Cached { layer: 0, offset: 1 },
            ],
            output: inner0(),
        };
        let layer = lower_single(rel);
        let (field, e) = single_output(&layer);
        assert_eq!(*field, FieldKind::Ext, "grand product is Ext");
        assert!(matches!(expr(&layer, e), Expr::Mul(_)), "read(a)·read(b) is a Mul");
    }

    #[test]
    fn unbalanced_grand_product_with_cache_is_ext_mul() {
        let rel = NoFieldGKRRelation::UnbalancedGrandProductWithCache {
            scalar: GKRAddress::Cached { layer: 0, offset: 0 },
            input: GKRAddress::Cached { layer: 0, offset: 1 },
            output: inner0(),
        };
        let layer = lower_single(rel);
        let (field, e) = single_output(&layer);
        assert_eq!(*field, FieldKind::Ext);
        assert!(matches!(expr(&layer, e), Expr::Mul(_)), "read(s)·read(t) is a Mul");
    }

    #[test]
    fn trivial_product_is_ext_mul() {
        let rel = NoFieldGKRRelation::TrivialProduct {
            input: [blw(0), blw(1)],
            output: inner0(),
        };
        let layer = lower_single(rel);
        let (field, e) = single_output(&layer);
        assert_eq!(*field, FieldKind::Ext);
        assert!(matches!(expr(&layer, e), Expr::Mul(_)), "read·read is a Mul");
    }

    #[test]
    fn initial_grand_product_without_caches_is_mul_of_two_tuples() {
        // Two memory tuples, each an affine Add over a permutation-additive
        // challenge; the product is the top-level Mul.
        let desc = NoFieldSpecialMemoryContributionRelation {
            address_space: CompiledAddressSpaceRelationStrict::Constant(1),
            address: CompiledAddressStrict::U32Space([0, 1]),
            timestamp: CompiledMemoryTimestamp::Zero,
            value: RamWordRepresentation::Zero,
            timestamp_offset: 0,
        };
        let rel = NoFieldGKRRelation::InitialGrandProductWithoutCaches {
            input: [desc.clone(), desc],
            output: inner0(),
        };
        let layer = lower_single(rel);
        let (field, e) = single_output(&layer);
        assert_eq!(*field, FieldKind::Ext);
        assert!(matches!(expr(&layer, e), Expr::Mul(_)), "tuple·tuple is a Mul");
        // The tuple carries the additive permutation challenge and the addr slots.
        assert!(has_permutation_additive(&layer), "tuple shifted by beta_perm");
        assert!(has_perm_slot(&layer, PermutationSlot::AddressLow));
        assert!(has_perm_slot(&layer, PermutationSlot::AddressHigh));
    }

    #[test]
    fn mask_into_identity_is_one_plus_mask_times_input_minus_one() {
        // 1 + mask·(input − 1): top-level Add of [Constant(1), Mul(mask, Add(input, -1))].
        let rel = NoFieldGKRRelation::MaskIntoIdentityProduct {
            input: blw(0),
            mask: blw(1),
            output: inner0(),
        };
        let layer = lower_single(rel);
        let (field, e) = single_output(&layer);
        assert_eq!(*field, FieldKind::Ext);
        // Top level is an Add: a constant `1` plus a product term.
        let Expr::Add(terms) = expr(&layer, e) else {
            panic!("mask gate top level must be Add, got {:?}", expr(&layer, e));
        };
        assert_eq!(terms.len(), 2, "1 + (mask·(input−1))");
        let has_const_one = terms.iter().any(|t| {
            matches!(expr(&layer, *t), Expr::Source(sid)
                if matches!(&layer.sources[sid.0 as usize].kind,
                    SourceKind::Constant { value: 1 }))
        });
        let has_mul = terms.iter().any(|t| matches!(expr(&layer, *t), Expr::Mul(_)));
        assert!(has_const_one && has_mul, "expected Constant(1) + Mul term");
    }

    // -- memory-tuple descriptor shapes (via sample_relation_cases) --

    #[test]
    fn memory_tuple_is_register_uses_one_minus_bit() {
        // IsRegister(0) → 1 − mem[0], i.e. an Add of [Constant(1), Mul(-1, mem[0])].
        let is_register = NoFieldSpecialMemoryContributionRelation {
            address_space: CompiledAddressSpaceRelationStrict::IsRegister(0),
            address: CompiledAddressStrict::U16Space(1),
            timestamp: CompiledMemoryTimestamp::Zero,
            value: RamWordRepresentation::Zero,
            timestamp_offset: 0,
        };
        let layer = lower_single(materialize_tuple(is_register));
        // The `1 − bit` register indicator interns a Constant(1) and a (-1)·mem[0]
        // product. Both must be present as sub-exprs somewhere in the tuple.
        let has_one = layer.sources.iter().any(|s| {
            matches!(&s.kind, SourceKind::Constant { value: 1 })
        });
        assert!(has_one, "IsRegister contributes a Constant(1) for `1 − bit`");
        // mem[0] is the address-space indicator bit.
        assert!(memory_reads(&layer).contains(&0), "reads the indicator bit mem[0]");
        // The address U16Space(1) reads mem[1] scaled by ch(AddressLow).
        assert!(memory_reads(&layer).contains(&1));
        assert!(has_perm_slot(&layer, PermutationSlot::AddressLow));
    }

    #[test]
    fn memory_tuple_is_ram_uses_bare_bit() {
        // IsRam(0) → mem[0] (no `1 −` wrapper around the indicator).
        let is_ram = NoFieldSpecialMemoryContributionRelation {
            address_space: CompiledAddressSpaceRelationStrict::IsRam(0),
            address: CompiledAddressStrict::U16Space(1),
            timestamp: CompiledMemoryTimestamp::Zero,
            value: RamWordRepresentation::Zero,
            timestamp_offset: 0,
        };
        let layer = lower_single(materialize_tuple(is_ram));
        // The indicator bit mem[0] is read directly. IsRam does NOT introduce the
        // `1 −` Constant that IsRegister does (only the Constant address space /
        // RAM const could) — here address space is IsRam and address is U16Space,
        // so no `Constant(1)` from the address-space term.
        assert!(memory_reads(&layer).contains(&0), "reads the indicator bit mem[0]");
        let has_one = layer.sources.iter().any(|s| {
            matches!(&s.kind, SourceKind::Constant { value: 1 })
        });
        assert!(!has_one, "IsRam contributes the bare bit, no `1 −` Constant");
    }

    #[test]
    fn memory_tuple_special_indirect_low_recomposes_low_address() {
        // U32SpaceSpecialIndirect: low limb = mem[low_base] + coeff·mem[dynamic]
        // (low_offset 0), high = mem[high]. coeff = 1 here, dynamic col = 1.
        let special = NoFieldSpecialMemoryContributionRelation {
            address_space: CompiledAddressSpaceRelationStrict::Constant(0),
            address: CompiledAddressStrict::U32SpaceSpecialIndirect {
                low_base: 0,
                low_dynamic_offset: Some((3, 1)),
                low_offset: 0,
                high: 2,
            },
            timestamp: CompiledMemoryTimestamp::Zero,
            value: RamWordRepresentation::Zero,
            timestamp_offset: 0,
        };
        let layer = lower_single(materialize_tuple(special));
        // low_base mem[0], dynamic mem[1], high mem[2] all read.
        let reads = memory_reads(&layer);
        assert!(reads.contains(&0) && reads.contains(&1) && reads.contains(&2));
        // coeff 3 appears as a Constant scaling the dynamic read.
        let has_coeff = layer.sources.iter().any(|s| {
            matches!(&s.kind, SourceKind::Constant { value: 3 })
        });
        assert!(has_coeff, "dynamic offset coeff `3` is a Constant factor");
        assert!(has_perm_slot(&layer, PermutationSlot::AddressLow));
        assert!(has_perm_slot(&layer, PermutationSlot::AddressHigh));
    }

    #[test]
    fn memory_tuple_u8_limbs_recomposes_each_value_limb() {
        // U8Limbs([b0,b1,b2,b3]) → value_low = mem[b0] + 2^8·mem[b1],
        // value_high = mem[b2] + 2^8·mem[b3]. The byte shift 2^8 is a Constant.
        let u8_limbs = NoFieldSpecialMemoryContributionRelation {
            address_space: CompiledAddressSpaceRelationStrict::Constant(0),
            address: CompiledAddressStrict::U16Space(0),
            timestamp: CompiledMemoryTimestamp::Zero,
            value: RamWordRepresentation::U8Limbs([10, 11, 12, 13]),
            timestamp_offset: 0,
        };
        let layer = lower_single(materialize_tuple(u8_limbs));
        let reads = memory_reads(&layer);
        for col in [10, 11, 12, 13] {
            assert!(reads.contains(&col), "byte column {col} read");
        }
        let has_byte_shift = layer.sources.iter().any(|s| {
            matches!(&s.kind, SourceKind::Constant { value: 256 })
        });
        assert!(has_byte_shift, "U8 recomposition multiplies high byte by 2^8 = 256");
        assert!(has_perm_slot(&layer, PermutationSlot::ValueLow));
        assert!(has_perm_slot(&layer, PermutationSlot::ValueHigh));
    }

    #[test]
    fn memory_tuple_timestamp_offset_is_added_to_low_limb() {
        // Normal timestamp with a non-zero offset: low limb is mem[ts0] + offset.
        let desc = NoFieldSpecialMemoryContributionRelation {
            address_space: CompiledAddressSpaceRelationStrict::Constant(0),
            address: CompiledAddressStrict::U16Space(0),
            timestamp: CompiledMemoryTimestamp::Normal([5, 6]),
            value: RamWordRepresentation::Zero,
            timestamp_offset: 7,
        };
        let layer = lower_single(materialize_tuple(desc));
        let reads = memory_reads(&layer);
        assert!(reads.contains(&5) && reads.contains(&6), "ts limbs read");
        let has_offset = layer.sources.iter().any(|s| {
            matches!(&s.kind, SourceKind::Constant { value: 7 })
        });
        assert!(has_offset, "timestamp_offset 7 is added to the low limb");
        assert!(has_perm_slot(&layer, PermutationSlot::TimestampLow));
        assert!(has_perm_slot(&layer, PermutationSlot::TimestampHigh));
    }

    // -- inits / teardowns: init (zeroed ts/value) vs teardown (limb reads) --

    #[test]
    fn inits_pair_is_ext_mul_of_two_virtual_setup_tuples_no_mem_reads() {
        // Init: zeroed timestamp/value → NO base-memory reads at all; address is
        // the inits/teardowns virtual setups. Output is an Ext Mul of two tuples.
        let rel = NoFieldGKRRelation::InitsOrTeardownsInitialPair {
            timestamp_and_value: InitsOrTeardownsTimestampAndValue::Init,
            setup: [
                GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
                GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
            ],
            output: inner0(),
            set_idxes: [0, 1],
        };
        let layer = lower_single(rel);
        let (field, e) = single_output(&layer);
        assert_eq!(*field, FieldKind::Ext);
        assert!(matches!(expr(&layer, e), Expr::Mul(_)), "init tuple·tuple is a Mul");
        assert!(
            memory_reads(&layer).is_empty(),
            "init has zeroed ts/value → no base-memory reads"
        );
        assert!(has_virtual_setup(&layer, VirtualSetupKind::InitsAndTeardownsLow));
        assert!(has_virtual_setup(&layer, VirtualSetupKind::InitsAndTeardownsHigh));
        assert!(has_permutation_additive(&layer));
        assert!(has_perm_slot(&layer, PermutationSlot::AddressLow));
        assert!(has_perm_slot(&layer, PermutationSlot::AddressHigh));
        // Init carries NO timestamp/value slots.
        assert!(!has_perm_slot(&layer, PermutationSlot::TimestampLow));
        assert!(!has_perm_slot(&layer, PermutationSlot::ValueLow));
    }

    #[test]
    fn teardown_pair_reads_timestamp_and_value_limbs() {
        // Teardown: timestamp/value limb indexes are read from base memory, and
        // the timestamp/value challenge slots appear.
        let rel = NoFieldGKRRelation::InitsOrTeardownsInitialPair {
            timestamp_and_value: InitsOrTeardownsTimestampAndValue::Teardown {
                lhs_timestamp: [0, 1],
                lhs_value: [2, 3],
                rhs_timestamp: [4, 5],
                rhs_value: [6, 7],
            },
            setup: [
                GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsLow),
                GKRAddress::VirtualSetup(VirtualSetupPoly::InitsAndTeardownsHigh),
            ],
            output: inner0(),
            set_idxes: [0, 1],
        };
        let layer = lower_single(rel);
        let (field, e) = single_output(&layer);
        assert_eq!(*field, FieldKind::Ext);
        assert!(matches!(expr(&layer, e), Expr::Mul(_)));
        // All eight ts/value limb columns are read from base memory.
        let reads = memory_reads(&layer);
        for col in 0..8 {
            assert!(reads.contains(&col), "teardown reads ts/value limb mem[{col}]");
        }
        assert!(has_perm_slot(&layer, PermutationSlot::TimestampLow));
        assert!(has_perm_slot(&layer, PermutationSlot::TimestampHigh));
        assert!(has_perm_slot(&layer, PermutationSlot::ValueLow));
        assert!(has_perm_slot(&layer, PermutationSlot::ValueHigh));
        // Still uses the inits/teardowns address virtual setups.
        assert!(has_virtual_setup(&layer, VirtualSetupKind::InitsAndTeardownsLow));
        assert!(has_virtual_setup(&layer, VirtualSetupKind::InitsAndTeardownsHigh));
    }

    // -- smoke: every memory/inits subcase in sample_relation_cases lowers --

    #[test]
    fn memory_and_inits_sample_cases_lower_to_single_ext_output() {
        for (name, rel) in sample_relation_cases() {
            let is_mem = name.starts_with("MemoryTuple")
                || name.starts_with("InitsOrTeardownsInitialPair");
            if !is_mem {
                continue;
            }
            let layer = lower_single(rel);
            let outs = outputs(&layer);
            assert_eq!(outs.len(), 1, "{name} is single-output");
            assert_eq!(outs[0].0, FieldKind::Ext, "{name} output is Ext");
            assert!(
                matches!(expr(&layer, outs[0].1), Expr::Mul(_)),
                "{name} is a grand-product Mul"
            );
        }
    }

    // ── Constraint / enforce lowering (Task 10) ──────────────────────────────

    /// True if any source is a `Challenge(ConstraintAggregation, ..)`.
    fn has_constraint_aggregation(layer: &DagLayer) -> bool {
        layer.sources.iter().any(|s| {
            matches!(&s.kind, SourceKind::Challenge { reference }
                if reference.key == ChallengeKey::ConstraintAggregation)
        })
    }

    /// Return the single constraint root's expr, asserting no Output roots
    /// exist. A constraint root is claim-only: `materialize: None`.
    fn single_constraint(layer: &DagLayer) -> ExprId {
        let constraints: Vec<&Root> = layer
            .roots
            .iter()
            .filter(|r| r.materialize.is_none())
            .collect();
        assert_eq!(constraints.len(), 1, "expected exactly one Constraint root");
        assert!(
            layer.roots.iter().all(|r| r.materialize.is_none()),
            "no Output roots should be present for a constraint relation"
        );
        constraints[0].expr
    }

    #[test]
    fn enforce_single_max_quadratic_produces_one_constraint_no_output() {
        // 1·x0·x1 + 2·x0 → Constraint root with quadratic+linear AddMul tree.
        let rel = NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint {
            input: NoFieldMaxQuadraticGKRRelation {
                quadratic_terms: vec![(blw(0), vec![(1u32, blw(1))].into_boxed_slice())]
                    .into_boxed_slice(),
                linear_terms: vec![(2u32, blw(0))].into_boxed_slice(),
                constant: 0,
            },
            expression: NoFieldStructuredExpression::Constant(0),
        };
        let layer = lower_single(rel);

        // Exactly one Constraint root, zero Output roots.
        let e = single_constraint(&layer);

        // RootOrigin recorded: slot is Constraint(0).
        assert_eq!(
            layer.roots[0].claim.as_ref().map(|c| &c.origin),
            Some(&RootOrigin {
                group: RootGroup::Gates,
                relation_index: 0,
                slot: RootSlot::Constraint(0),
            })
        );

        // No sink was allocated (constraint roots never materialize).
        assert!(
            layer.roots.iter().all(|r| r.materialize.is_none()),
            "Constraint root must not create a sink"
        );

        // The top-level expr is an Add (quadratic + linear terms).
        assert!(
            matches!(layer.exprs[e.0 as usize], Expr::Add(_)),
            "single constraint expr top level is Add, got {:?}",
            layer.exprs[e.0 as usize]
        );
        // No ConstraintAggregation challenge — single constraint uses no rho.
        assert!(
            !has_constraint_aggregation(&layer),
            "single constraint does not use the rho challenge"
        );
    }

    #[test]
    fn enforce_single_max_quadratic_constant_only_is_bare_source() {
        // Constant-only (non-zero) → a single Constant Source.
        let rel = NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint {
            input: NoFieldMaxQuadraticGKRRelation {
                quadratic_terms: vec![].into_boxed_slice(),
                linear_terms: vec![].into_boxed_slice(),
                constant: 5,
            },
            expression: NoFieldStructuredExpression::Constant(0),
        };
        let layer = lower_single(rel);
        let e = single_constraint(&layer);
        // Must be a bare Constant(5) source.
        assert!(
            matches!(&layer.exprs[e.0 as usize], Expr::Source(sid)
                if matches!(&layer.sources[sid.0 as usize].kind,
                    SourceKind::Constant { value: 5 })),
            "constant-only single constraint is a bare Constant source"
        );
    }

    #[test]
    fn enforce_constraints_max_quadratic_produces_one_constraint_no_output() {
        // Batched: one quadratic term with one (c=1, p=1) power.
        let rel = NoFieldGKRRelation::EnforceConstraintsMaxQuadratic {
            input: crate::gkr_compiler::NoFieldMaxQuadraticConstraintsGKRRelation {
                quadratic_terms: vec![
                    ((blw(0), blw(1)), vec![(1u32, 1usize)].into_boxed_slice()),
                ]
                .into_boxed_slice(),
                linear_terms: vec![].into_boxed_slice(),
                constants: vec![].into_boxed_slice(),
            },
        };
        let layer = lower_single(rel);

        // Exactly one Constraint root, zero Output roots.
        let _e = single_constraint(&layer);

        // RootOrigin slot is Constraint(0).
        assert_eq!(
            layer.roots[0].claim.as_ref().map(|c| c.origin.slot.clone()),
            Some(RootSlot::Constraint(0))
        );

        // No sink allocated.
        assert!(
            layer.roots.iter().all(|r| r.materialize.is_none()),
            "batched constraint must not create a sink"
        );

        // ConstraintAggregation challenge present (rho^1 = One).
        assert!(
            has_constraint_aggregation(&layer),
            "batched constraint must intern a ConstraintAggregation challenge"
        );
    }

    #[test]
    fn enforce_constraints_max_quadratic_contains_rho_challenge() {
        // Batched: linear term at power 2 → rho^2 = Static(2).
        use crate::gkr_compiler::dag_ir::ChallengePower;
        let rel = NoFieldGKRRelation::EnforceConstraintsMaxQuadratic {
            input: crate::gkr_compiler::NoFieldMaxQuadraticConstraintsGKRRelation {
                quadratic_terms: vec![].into_boxed_slice(),
                linear_terms: vec![
                    (blw(0), vec![(3u32, 2usize)].into_boxed_slice()),
                ]
                .into_boxed_slice(),
                constants: vec![(5u32, 1usize)].into_boxed_slice(),
            },
        };
        let layer = lower_single(rel);
        single_constraint(&layer);

        // rho^1 (One) present for the constant term.
        assert!(
            layer.sources.iter().any(|s| matches!(&s.kind,
                SourceKind::Challenge { reference }
                    if reference.key == ChallengeKey::ConstraintAggregation
                        && reference.power == ChallengePower::One)),
            "constant term at p=1 → Challenge(ConstraintAggregation, One)"
        );
        // rho^2 (Static(2)) present for the linear term.
        assert!(
            layer.sources.iter().any(|s| matches!(&s.kind,
                SourceKind::Challenge { reference }
                    if reference.key == ChallengeKey::ConstraintAggregation
                        && reference.power == ChallengePower::Static(2))),
            "linear term at p=2 → Challenge(ConstraintAggregation, Static(2))"
        );
    }

    #[test]
    fn enforce_constraints_max_quadratic_empty_is_constant_zero() {
        // Empty relation: all three slices are empty → Constant(0).
        let rel = NoFieldGKRRelation::EnforceConstraintsMaxQuadratic {
            input: crate::gkr_compiler::NoFieldMaxQuadraticConstraintsGKRRelation {
                quadratic_terms: vec![].into_boxed_slice(),
                linear_terms: vec![].into_boxed_slice(),
                constants: vec![].into_boxed_slice(),
            },
        };
        let layer = lower_single(rel);
        let e = single_constraint(&layer);
        assert!(
            matches!(&layer.exprs[e.0 as usize], Expr::Source(sid)
                if matches!(&layer.sources[sid.0 as usize].kind,
                    SourceKind::Constant { value: 0 })),
            "empty batched constraint is Constant(0)"
        );
        assert!(!has_constraint_aggregation(&layer), "empty → no rho source");
    }

    #[test]
    fn constraint_variant_smoke_lower_without_err() {
        // Both constraint variants in sample_relations lower without Err.
        for (name, rel) in sample_relations() {
            if name != "EnforceSingleMaxQuadraticConstraint"
                && name != "EnforceConstraintsMaxQuadratic"
            {
                continue;
            }
            let artifact = single_relation_artifact(rel);
            assert!(
                lower_dag(&artifact).is_ok(),
                "{name} must lower without Err"
            );
        }
    }

    // ── Caches + batching order (Task 11): whole add_sub artifact ─────────────

    use crate::gkr_compiler::test_support::build_add_sub_artifact;

    /// A root is a materialize-only cache root (`materialize: Some(Cache)`).
    fn is_cache_root(root: &Root) -> bool {
        matches!(&root.materialize, Some(s) if matches!(s.kind, SinkKind::Cache { .. }))
    }

    /// Count of claim-bearing roots (`claim: Some` — every non-cache Output plus
    /// every Constraint).
    fn claim_bearing_count(layer: &DagLayer) -> usize {
        layer.roots.iter().filter(|r| r.claim.is_some()).count()
    }

    /// The whole add_sub artifact (the cache variant) lowers without `Err`.
    #[test]
    fn add_sub_artifact_lowers_without_err() {
        let artifact = build_add_sub_artifact();
        assert!(
            lower_dag(&artifact).is_ok(),
            "the whole add_sub artifact must lower without Err"
        );
    }

    /// The cache variant must actually contain caches; otherwise the cache tests
    /// below vacuously pass. (Guards against a fixture regression.)
    #[test]
    fn add_sub_artifact_has_caches() {
        let artifact = build_add_sub_artifact();
        let total_caches: usize = artifact
            .layers
            .iter()
            .map(|l| l.cached_relations.len())
            .sum();
        assert!(
            total_caches > 0,
            "the cache variant must materialize at least one cache"
        );
    }

    /// Cache roots: `Cache` sink, ABSENT from `batching.roots` and `origins`.
    #[test]
    fn cache_roots_have_cache_sinks_and_no_beta_no_origin() {
        let artifact = build_add_sub_artifact();
        let circuit = lower_dag(&artifact).expect("lower_dag must succeed");

        let mut saw_cache_root = false;
        for layer in &circuit.layers {
            // The number of cache roots equals the number of cached relations in
            // the source layer (each materializes exactly one root).
            let n_cache_roots = layer
                .roots
                .iter()
                .filter(|r| is_cache_root(r))
                .count();

            for (i, root) in layer.roots.iter().enumerate() {
                let id = RootId(i as u32);
                if is_cache_root(root) {
                    saw_cache_root = true;
                    // Materialization-only: no beta power, no claim/origin.
                    assert!(
                        !layer.batching.roots.contains(&id),
                        "cache root {id:?} must be absent from the batching order"
                    );
                    assert!(
                        root.claim.is_none(),
                        "cache root {id:?} must have no RootOrigin"
                    );
                }
            }

            // Cache roots occupy the LEADING RootId slots (materialized first).
            for i in 0..n_cache_roots {
                assert!(
                    is_cache_root(&layer.roots[i]),
                    "cache roots must be the leading roots in the layer"
                );
            }
        }
        assert!(saw_cache_root, "expected at least one cache root across layers");
    }

    /// `batching.roots.len()` equals the claim-bearing root count per layer.
    #[test]
    fn batching_len_equals_claim_bearing_root_count() {
        let artifact = build_add_sub_artifact();
        let circuit = lower_dag(&artifact).expect("lower_dag must succeed");
        for layer in &circuit.layers {
            assert_eq!(
                layer.batching.roots.len(),
                claim_bearing_count(layer),
                "batching order length must equal the claim-bearing root count"
            );
            // The batching order is exactly the non-cache roots in emission order.
            let expected: Vec<RootId> = (0..layer.roots.len() as u32)
                .map(RootId)
                .filter(|id| !is_cache_root(&layer.roots[id.0 as usize]))
                .collect();
            assert_eq!(
                layer.batching.roots, expected,
                "batching order must be the non-cache roots in emission order"
            );
            // Every batched root carries a claim/origin; cache roots never do.
            for id in &layer.batching.roots {
                assert!(
                    layer.roots[id.0 as usize].claim.is_some(),
                    "every claim-bearing root must have a RootOrigin"
                );
            }
        }
    }

    /// Task 2 attribute-shape invariant: the dissolved `Root` struct carries
    /// orthogonal `materialize`/`claim` attributes. A cache root is
    /// materialize-only (`Some(Cache)`, `claim: None`) and never batched; a
    /// claim-bearing root carries `claim: Some(..)` and appears in the batching
    /// order exactly once. No other attribute shape is produced by lowering.
    #[test]
    fn cache_is_materialize_only_claims_are_batched() {
        let artifact = build_add_sub_artifact();
        let dag = lower_dag(&artifact).expect("lower_dag");
        for layer in &dag.layers {
            for (i, root) in layer.roots.iter().enumerate() {
                let rid = RootId(i as u32);
                let in_batching = layer.batching.roots.contains(&rid);
                match (&root.materialize, &root.claim) {
                    // Cache: materialize-only, never batched.
                    (Some(s), None) if matches!(s.kind, SinkKind::Cache { .. }) => {
                        assert!(!in_batching, "cache root {rid:?} must be absent from batching");
                    }
                    // Claim-bearing: in batching exactly once.
                    (_, Some(_)) => {
                        assert!(in_batching, "claim-bearing root {rid:?} must be in batching");
                    }
                    other => panic!("unexpected root attribute shape: {other:?}"),
                }
            }
        }
    }

    /// Structural invariant (Task 1, secondary): cache reuse is DAG sharing.
    /// A same-layer cache value is materialized by a `Cache`-sink root AND its
    /// `ExprId` is shared (reachable through the pure expr DAG) by at least one
    /// claim-bearing root's cone — never an opaque separate-source leaf.
    ///
    /// (`SourceKind::Prior` was removed in Task 1, so a "no Prior sources" check
    /// is now enforced by the type system; this asserts the positive sharing
    /// property instead. The primary value/alias-identity gate lives prover-side
    /// in `dag_ir_differential::cache_consumer_value_and_alias_identity`.)
    #[test]
    fn lowering_shares_cache_exprs_with_consumers() {
        // Walk the pure expr DAG (Add/Mul operands + LookupValue.query), NOT any
        // root edge: a shared cache value is reachable this way iff the consumer
        // references its ExprId directly.
        fn cone_contains(layer: &DagLayer, start: ExprId, target: ExprId) -> bool {
            let mut stack = vec![start];
            let mut seen = std::collections::HashSet::new();
            while let Some(id) = stack.pop() {
                if id == target {
                    return true;
                }
                if !seen.insert(id.0) {
                    continue;
                }
                match &layer.exprs[id.0 as usize] {
                    Expr::Source(src_id) => {
                        if let SourceKind::LookupValue { query, .. } =
                            &layer.sources[src_id.0 as usize].kind
                        {
                            stack.push(*query);
                        }
                    }
                    Expr::Add(args) | Expr::Mul(args) => stack.extend_from_slice(args),
                }
            }
            false
        }
        fn root_expr(root: &Root) -> ExprId {
            root.expr
        }

        let artifact = build_add_sub_artifact();
        let circuit = lower_dag(&artifact).expect("lower_dag must succeed");

        let mut found = false;
        for layer in &circuit.layers {
            let cache_exprs: Vec<ExprId> = layer
                .roots
                .iter()
                .filter(|r| is_cache_root(r))
                .map(root_expr)
                .collect();
            for &consumer_id in &layer.batching.roots {
                let consumer_expr = root_expr(&layer.roots[consumer_id.0 as usize]);
                for &cache_expr in &cache_exprs {
                    if cone_contains(layer, consumer_expr, cache_expr) {
                        found = true;
                    }
                }
            }
        }
        assert!(
            found,
            "a claim-bearing root must SHARE a same-layer cache root's ExprId \
             (cache reuse must be DAG sharing)"
        );
    }

    #[test]
    fn check_decoder_masks_rejects_wrong_mask() {
        use crate::definitions::gkr::{NoFieldVectorLookupRelation, DECODER_LOOKUP_FORMAL_SET_INDEX};
        let vec_rel = NoFieldVectorLookupRelation {
            columns: Box::new([]), // content irrelevant to the guard; only set_index matters
            lookup_set_index: DECODER_LOOKUP_FORMAL_SET_INDEX,
        };
        let rel = NoFieldGKRRelation::LookupWithDensAndCachedSetup {
            input: (GKRAddress::BaseLayerMemory(99), vec_rel), // mask 99 ≠ execute 7
            setup: (GKRAddress::Setup(0), GKRAddress::Setup(1)),
            output: [
                GKRAddress::InnerLayer { layer: 0, offset: 0 },
                GKRAddress::InnerLayer { layer: 0, offset: 1 },
            ],
        };
        let relations = [rel];
        let res = check_decoder_masks(
            relations.iter(),
            &BTreeMap::new(),
            Some(GKRAddress::BaseLayerMemory(7)),
        );
        assert!(res.is_err(), "decoder mask ≠ machine_state.execute must be rejected");
    }

    /// `LookupWithCachedDensAndSetup` is the LIVE cached-consumer path: the
    /// decoder fold is held in `cached_relations[input[1]]` as a
    /// `VectorizedLookup` with `lookup_set_index == DECODER_LOOKUP_FORMAL_SET_INDEX`,
    /// and `input[0]` is the mask. Verify that a wrong mask is rejected even
    /// through this cached lookup path (no inline `NoFieldVectorLookupRelation`).
    #[test]
    fn check_decoder_masks_rejects_wrong_mask_cached() {
        use crate::definitions::gkr::{NoFieldVectorLookupRelation, DECODER_LOOKUP_FORMAL_SET_INDEX};

        // Cache address that will hold the decoder VectorizedLookup.
        let cache_addr = GKRAddress::Cached { layer: 0, offset: 0 };

        // The cached relation: a VectorizedLookup keyed to the decoder set index.
        let decoder_vl = NoFieldGKRCacheRelation::VectorizedLookup(NoFieldVectorLookupRelation {
            columns: Box::new([]),
            lookup_set_index: DECODER_LOOKUP_FORMAL_SET_INDEX,
        });

        let mut cached_relations: BTreeMap<GKRAddress, NoFieldGKRCacheRelation> = BTreeMap::new();
        cached_relations.insert(cache_addr, decoder_vl);

        // The gate: input[1] = cache_addr (decoder), input[0] = wrong mask (col 99).
        let rel = NoFieldGKRRelation::LookupWithCachedDensAndSetup {
            input: [GKRAddress::BaseLayerMemory(99), cache_addr], // mask 99 ≠ execute 7
            setup: [GKRAddress::Setup(0), GKRAddress::Setup(1)],
            output: [
                GKRAddress::InnerLayer { layer: 0, offset: 0 },
                GKRAddress::InnerLayer { layer: 0, offset: 1 },
            ],
        };

        let relations = [rel];
        let res = check_decoder_masks(
            relations.iter(),
            &cached_relations,
            Some(GKRAddress::BaseLayerMemory(7)), // expected execute column = 7
        );
        assert!(
            res.is_err(),
            "cached-consumer path: decoder mask (col 99) ≠ machine_state.execute (col 7) must be rejected"
        );
    }

    // ── B1: insert_resolution CSE-collision ───────────────────────────────────

    /// Inserting the same leaf with a DIFFERENT strategy must return Err("CSE collision");
    /// re-inserting with the SAME strategy is idempotent (Ok).
    #[test]
    fn insert_resolution_rejects_cse_collision() {
        let mut out = LayerOut::new();
        // First insert: Ok.
        out.insert_resolution(ExprId(0), ResolutionStrategy::PeekSetup).expect("first insert must succeed");
        // Idempotent re-insert of the same strategy: Ok.
        out.insert_resolution(ExprId(0), ResolutionStrategy::PeekSetup).expect("idempotent re-insert must succeed");
        // Different strategy at the same leaf: CSE collision → Err.
        let err = out.insert_resolution(ExprId(0), ResolutionStrategy::PeekAggregate { set_index: 3 })
            .expect_err("conflicting strategy must be rejected");
        assert!(err.contains("CSE collision"), "error must mention CSE collision, got: {err}");
    }
}
