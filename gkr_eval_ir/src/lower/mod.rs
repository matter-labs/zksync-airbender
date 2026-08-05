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

use cs::definitions::gkr::DECODER_LOOKUP_FORMAL_SET_INDEX;
use cs::definitions::{GKRAddress, VirtualSetupPoly};
use cs::gkr_compiler::{
    GKRCircuitArtifact, GateArtifacts, NoFieldGKRCacheRelation, NoFieldGKRRelation,
};

use super::{
    simplify::SIMPLIFY_MODULUS, simplify_circuit, ArenaBuilder, BatchingOrder, ClaimInfo,
    DagCircuit, DagGlobals, DagLayer, ExprId, FieldKind, FillSource, RangeWidth, ReadPlace,
    ResolutionStrategy, Root, RootExecution, RootGroup, RootId, RootOrigin, RootSlot, SinkInfo,
    SinkKind, SourceKind, VirtualSetupKind,
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
        // PeekDecoder is only ever emitted for a decoder-set fold that was
        // reached via a masked consumer (LookupWithDensAndSetupExpressions /
        // LookupWithDensAndCachedSetup). The mask is enforced upstream by
        // check_decoder_masks, so an unmasked decoder fold cannot occur on the
        // real pipeline — any decoder consumer that bypasses the mask guard
        // is a generator bug caught before this point.
        let strat = if set_index == DECODER_LOOKUP_FORMAL_SET_INDEX {
            let predicate = decoder_predicate
                .ok_or_else(|| {
                    "dag_ir: decoder lookup fold but circuit has no machine_state predicate"
                        .to_string()
                })?
                .clone();
            ResolutionStrategy::PeekDecoder {
                predicate,
                fill: FillSource::DecoderLookupFill,
            }
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
fn lower_relation<F: PrimeField>(
    arena: &mut ArenaBuilder,
    out: &mut LayerOut,
    rel: &NoFieldGKRRelation<F>,
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
            out.record_vector(
                expr,
                input.lookup_set_index,
                input.columns.len(),
                decoder_predicate,
            )?;
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
            out.record_vector(
                b,
                input[0].lookup_set_index,
                input[0].columns.len(),
                decoder_predicate,
            )?;
            out.record_vector(
                d,
                input[1].lookup_set_index,
                input[1].columns.len(),
                decoder_predicate,
            )?;
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
            out.record_vector(
                b,
                input.lookup_set_index,
                input.columns.len(),
                decoder_predicate,
            )?;
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
            out.record_vector(
                b,
                input.1.lookup_set_index,
                input.1.columns.len(),
                decoder_predicate,
            )?;
            let c = lookup::read(arena, setup.0);
            let d = lookup::folded_setup(arena, &setup.1);
            out.record_setup(d, setup.1.len())?;
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
            out.record_vector(
                d,
                remainder.lookup_set_index,
                remainder.columns.len(),
                decoder_predicate,
            )?;
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
fn lower_cache<F: PrimeField>(
    arena: &mut ArenaBuilder,
    out: &mut LayerOut,
    addr: GKRAddress,
    rel: &NoFieldGKRCacheRelation<F>,
    minus_one: u32,
    decoder_predicate: Option<&ReadPlace>,
) -> Result<(RootId, ExprId), String> {
    use NoFieldGKRCacheRelation as C;
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
    let root_id = out.emit_cache(expr, addr, field)?;
    Ok((root_id, expr))
}

/// Every decoder-lookup consumer must use the global `machine_state.execute` as
/// its mask. `expected_mask == None` ⇒ the circuit has no machine state, so ANY
/// decoder consumer is an error. Inline consumers carry the decoder fold in
/// `input.1` (mask = `input.0`); the cached consumer reads a decoder
/// `VectorizedLookup` cache leaf via `input[1]` (mask = `input[0]`).
fn check_decoder_masks<'a, F: PrimeField + 'a>(
    relations: impl Iterator<Item = &'a NoFieldGKRRelation<F>>,
    cached_relations: &BTreeMap<GKRAddress, NoFieldGKRCacheRelation<F>>,
    expected_mask: Option<GKRAddress>,
) -> Result<(), String> {
    use NoFieldGKRCacheRelation as C;
    use NoFieldGKRRelation as R;
    let assert_mask = |mask: GKRAddress| -> Result<(), String> {
        match expected_mask {
            Some(exp) if exp == mask => Ok(()),
            Some(exp) => Err(format!(
                "dag_ir: decoder mask {:?} != machine_state.execute {:?}",
                mask, exp
            )),
            None => Err(format!(
                "dag_ir: decoder consumer with mask {:?} but no machine_state",
                mask
            )),
        }
    };
    for rel in relations {
        match rel {
            R::LookupWithDensAndSetupExpressions { input, .. } => {
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
    let minus_one = F::CHARACTERISTICS_U32 - 1;

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
        let (_root_id, expr) = lower_cache(
            &mut arena,
            &mut out,
            *addr,
            rel,
            minus_one,
            decoder_predicate.as_ref(),
        )?;
        cache_aliases.insert(*addr, expr); // alias → shared ExprId (was: root_id)
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

fn root_execution<F: PrimeField>(
    artifact: &GKRCircuitArtifact<F>,
    layer_index: usize,
    layer: &DagLayer,
) -> Result<BTreeMap<RootId, RootExecution>, String> {
    let artifact_layer = &artifact.layers[layer_index];
    let mut execution = BTreeMap::new();
    for (index, root) in layer.roots.iter().enumerate() {
        let Some(claim) = &root.claim else { continue };
        let gates = match claim.origin.group {
            RootGroup::Gates => &artifact_layer.gates,
            RootGroup::GatesExternal => &artifact_layer.gates_with_external_connections,
        };
        let relation = &gates[claim.origin.relation_index].enforced_relation;
        let semantics = match relation {
            NoFieldGKRRelation::MaxQuadratic { output, .. }
                if artifact.scratch_space_mapping.contains_key(output) =>
            {
                Some(RootExecution::Preinitialized)
            }
            NoFieldGKRRelation::CopyInBaseField { input, .. }
            | NoFieldGKRRelation::CopyInExtensionField { input, .. } => match map_address(*input) {
                SourceKind::Read { place } => Some(RootExecution::Alias { source: place }),
                other => {
                    return Err(format!(
                        "dag_ir: copy root {index} has no readable source: {other:?}"
                    ));
                }
            },
            _ => None,
        };
        if let Some(semantics) = semantics {
            execution.insert(RootId(index as u32), semantics);
        }
    }
    Ok(execution)
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
    if F::CHARACTERISTICS_U32 as u64 != SIMPLIFY_MODULUS {
        return Err(format!(
            "dag_ir: simplify pass is hardcoded to modulus {SIMPLIFY_MODULUS} (BabyBear) but \
             field characteristic is {}; dag_ir simplify would silently const-fold mod the wrong prime",
            F::CHARACTERISTICS_U32
        ));
    }
    let layers = (0..artifact.layers.len())
        .map(|i| lower_layer(artifact, i, LowerMode::Simplified))
        .collect::<Result<Vec<_>, _>>()?;
    let root_execution = layers
        .iter()
        .enumerate()
        .map(|(index, layer)| root_execution(artifact, index, layer))
        .collect::<Result<Vec<_>, _>>()?;

    let dag = DagCircuit {
        layers,
        globals: DagGlobals {
            trace_len: artifact.trace_len,
            scratch: BTreeMap::new(),
            root_execution,
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
    if F::CHARACTERISTICS_U32 as u64 != SIMPLIFY_MODULUS {
        return Err(format!(
            "dag_ir: simplify pass is hardcoded to modulus {SIMPLIFY_MODULUS} (BabyBear) but \
             field characteristic is {}; dag_ir simplify would silently const-fold mod the wrong prime",
            F::CHARACTERISTICS_U32
        ));
    }
    let layers = (0..artifact.layers.len())
        .map(|i| lower_layer(artifact, i, LowerMode::Legacy))
        .collect::<Result<Vec<_>, _>>()?;
    let root_execution = layers
        .iter()
        .enumerate()
        .map(|(index, layer)| root_execution(artifact, index, layer))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(DagCircuit {
        layers,
        globals: DagGlobals {
            trace_len: artifact.trace_len,
            scratch: BTreeMap::new(),
            root_execution,
        },
    })
}
