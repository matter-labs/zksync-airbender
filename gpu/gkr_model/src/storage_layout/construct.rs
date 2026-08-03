//! Builds a [`GpuGKRStorageLayout`] by walking a compiled GKR artifact and
//! grouping every gate/cache-relation output by the storage layer +
//! `(AddressClass, FieldType)` slot it lives at.

use std::collections::{BTreeMap, BTreeSet};

use crate::address_audit::{
    classify, collect_addresses_from_cache_relation, collect_addresses_from_relation, AddressClass,
    GKR_MAX_POLYS_PER_SLOT,
};
use crate::upstream::{
    GKRAddress, GKRCircuitArtifact, NoFieldGKRCacheRelation, NoFieldGKRRelation, PrimeField,
};

use super::alias::build_alias_redirects;
use super::tower::append_tower_layers;
use super::types::{FieldType, GpuGKRLayerLayout, GpuGKRStorageLayout, StorageSlot};

impl GpuGKRStorageLayout {
    /// Build the layout from artifact gates only. Tower-layer entries are
    /// **not** included; allocators will panic on tower-layer addresses.
    /// Use [`Self::from_artifact_with_tower`] for the production path.
    #[doc(hidden)]
    pub fn from_artifact<F: PrimeField>(artifact: &GKRCircuitArtifact<F>) -> Self {
        Self::from_artifact_inner(artifact, None)
    }

    /// Build the layout from artifact gates and append tower-layer entries
    /// for the dim-reducing forward chain. Each tower layer carries its own
    /// `log2_stride` (halving each round, starting from
    /// `log2(trace_len) - 1`).
    pub fn from_artifact_with_tower<F: PrimeField>(
        artifact: &GKRCircuitArtifact<F>,
        final_trace_log_2: usize,
    ) -> Self {
        Self::from_artifact_inner(artifact, Some(final_trace_log_2))
    }

    fn from_artifact_inner<F: PrimeField>(
        artifact: &GKRCircuitArtifact<F>,
        tower_final_trace_log_2: Option<usize>,
    ) -> Self {
        assert!(
            artifact.trace_len.is_power_of_two() && artifact.trace_len > 0,
            "trace_len must be a positive power of two; got {}",
            artifact.trace_len
        );
        let log2_stride = artifact.trace_len.trailing_zeros();

        // Walk every gate across every artifact layer, grouping writes by the
        // storage layer the address lives at (`addr.layer` for InnerLayer /
        // Cached, `0` for trace-holder-backed addresses). A single artifact
        // layer drives writes one layer ahead, so we cannot simply use the
        // artifact's iteration index as the storage layer.
        let mut writes_by_storage_layer: BTreeMap<
            usize,
            BTreeMap<StorageSlot, BTreeSet<GKRAddress>>,
        > = BTreeMap::new();

        let aliases = build_alias_redirects(artifact);

        let record =
            |writes_map: &mut BTreeMap<usize, BTreeMap<StorageSlot, BTreeSet<GKRAddress>>>,
             addr: GKRAddress,
             field: FieldType| {
                if matches!(addr, GKRAddress::VirtualSetup(_)) {
                    return;
                }
                if aliases.contains_key(&addr) {
                    return;
                }
                let storage_layer = address_storage_layer(addr);
                let class = classify(&addr, storage_layer);
                writes_map
                    .entry(storage_layer)
                    .or_default()
                    .entry(StorageSlot { class, field })
                    .or_default()
                    .insert(addr);
            };

        for layer in artifact.layers.iter() {
            for gate in layer
                .gates
                .iter()
                .chain(layer.gates_with_external_connections.iter())
            {
                for (addr, field) in relation_outputs(&gate.enforced_relation) {
                    record(&mut writes_by_storage_layer, addr, field);
                }
            }
            for (cache_addr, cache_rel) in layer.cached_relations.iter() {
                let field = cache_relation_output_type(cache_rel);
                record(&mut writes_by_storage_layer, *cache_addr, field);
            }
        }

        // Layer-0 trace-holder-backed read sources referenced by any gate in
        // layer 0 (witness / memory / setup / scratch). Layer-0 gates are the
        // only consumers of these addresses; deeper layers read transformed
        // copies via Cached / InnerLayer.
        if let Some(layer_0) = artifact.layers.first() {
            let mut reads = Vec::new();
            for gate in layer_0
                .gates
                .iter()
                .chain(layer_0.gates_with_external_connections.iter())
            {
                let mut writes_unused = Vec::new();
                collect_addresses_from_relation(
                    &gate.enforced_relation,
                    &mut reads,
                    &mut writes_unused,
                );
            }
            for cache_rel in layer_0.cached_relations.values() {
                collect_addresses_from_cache_relation(cache_rel, &mut reads);
            }
            for addr in reads {
                match addr {
                    GKRAddress::BaseLayerWitness(_)
                    | GKRAddress::BaseLayerMemory(_)
                    | GKRAddress::Setup(_)
                    | GKRAddress::ScratchSpace(_) => {
                        record(&mut writes_by_storage_layer, addr, FieldType::Base);
                    }
                    _ => {}
                }
            }
        }
        // Scratch addresses materialized into layer 0 may appear via
        // `scratch_space_mapping_rev` even when no layer-0 gate references
        // them directly.
        for scratch_addr in artifact.scratch_space_mapping_rev.values() {
            if let GKRAddress::ScratchSpace(_) = scratch_addr {
                record(&mut writes_by_storage_layer, *scratch_addr, FieldType::Base);
            }
        }

        let max_layer = writes_by_storage_layer.keys().copied().max().unwrap_or(0);
        let n_layers = (max_layer + 1).max(artifact.layers.len());
        let mut layers = vec![
            GpuGKRLayerLayout {
                log2_stride,
                ..GpuGKRLayerLayout::default()
            };
            n_layers
        ];
        for (layer_idx, writes_per_slot) in writes_by_storage_layer {
            layers[layer_idx] =
                build_layer_layout_from_writes(layer_idx, &writes_per_slot, log2_stride);
        }

        if let Some(final_trace_log_2) = tower_final_trace_log_2 {
            append_tower_layers(
                &mut layers,
                artifact,
                log2_stride as usize,
                final_trace_log_2,
            );
        }

        let layout = Self {
            trace_len: artifact.trace_len,
            artifact_log2_stride: log2_stride,
            layers,
            aliases,
            scratch_space_mapping_rev: artifact.scratch_space_mapping_rev.clone(),
        };
        layout.assert_within_phase0_budgets();
        layout.assert_aliases_resolve();
        layout
    }
}

/// Returns the storage layer at which a poly with this address lives:
/// `0` for trace-holder-backed and scratch-space addresses, and the address's
/// `layer` field for `InnerLayer` / `Cached`.
pub fn address_storage_layer(addr: GKRAddress) -> usize {
    match addr {
        GKRAddress::BaseLayerWitness(_)
        | GKRAddress::BaseLayerMemory(_)
        | GKRAddress::Setup(_)
        | GKRAddress::VirtualSetup(_)
        | GKRAddress::ScratchSpace(_) => 0,
        GKRAddress::InnerLayer { layer, .. } | GKRAddress::Cached { layer, .. } => layer,
    }
}

fn build_layer_layout_from_writes(
    layer_idx: usize,
    writes_per_slot: &BTreeMap<StorageSlot, BTreeSet<GKRAddress>>,
    log2_stride: u32,
) -> GpuGKRLayerLayout {
    let mut layout = GpuGKRLayerLayout {
        log2_stride,
        ..GpuGKRLayerLayout::default()
    };
    for (slot, addrs) in writes_per_slot.iter() {
        // Trace-holder-backed slots (BaseLayerWitness / BaseLayerMemory /
        // Setup) and the externally-backed ScratchSpace slot must use
        // poly_idx == column index, so that the consolidated backing's view
        // at offset `poly_idx * trace_len` lines up with the trace holder /
        // scratch trace's column-major hypercube layout. For dynamic
        // forward-output slots we assign poly_idx by the BTreeSet's
        // deterministic iteration order.
        let trace_holder_aligned = matches!(
            slot.class,
            AddressClass::BaseLayerWitness
                | AddressClass::BaseLayerMemory
                | AddressClass::Setup
                | AddressClass::ScratchSpace
        );
        let mut max_assigned: u32 = 0;
        for (sequential_idx, addr) in addrs.iter().enumerate() {
            let poly_idx = if trace_holder_aligned {
                column_index_for_layer0(addr)
            } else {
                sequential_idx as u32
            };
            assert!(
                (poly_idx as usize) < GKR_MAX_POLYS_PER_SLOT,
                "poly_idx {poly_idx} out of range for slot {:?}/{} (max {})",
                slot.class,
                slot.field.label(),
                GKR_MAX_POLYS_PER_SLOT
            );
            let prev = layout
                .index
                .insert(*addr, (slot.class, slot.field, poly_idx));
            assert!(
                prev.is_none(),
                "duplicate layout entry for address {:?} at layer {layer_idx}",
                addr
            );
            max_assigned = max_assigned.max(poly_idx + 1);
        }
        // For trace-holder-aligned slots the recorded count is a strict lower
        // bound on the externally-provided backing capacity (the actual
        // capacity is `columns_count * trace_len`, which may exceed
        // `max_referenced_column + 1`). For dynamic slots the count is the
        // exact size of the freshly-allocated consolidated backing.
        let count = if trace_holder_aligned {
            max_assigned
        } else {
            addrs.len() as u32
        };
        layout.slot_poly_counts.insert(*slot, count);
    }
    layout
}

fn cache_relation_output_type<F: PrimeField>(rel: &NoFieldGKRCacheRelation<F>) -> FieldType {
    use NoFieldGKRCacheRelation::*;
    match rel {
        SingleColumnLookup { .. } => FieldType::Base,
        VectorizedLookup(_) | VectorizedLookupSetup(_) | MemoryTuple(_) => FieldType::Ext,
    }
}

fn column_index_for_layer0(addr: &GKRAddress) -> u32 {
    let col = match addr {
        GKRAddress::BaseLayerWitness(col)
        | GKRAddress::BaseLayerMemory(col)
        | GKRAddress::Setup(col)
        | GKRAddress::ScratchSpace(col) => *col,
        _ => unreachable!(
            "column_index_for_layer0 called on non-trace-holder address {:?}",
            addr
        ),
    };
    // Checked cast: a naive `as u32` would silently truncate (and thus alias
    // two distinct large column indices onto the same `poly_idx`) instead of
    // failing, which is exactly the kind of silent corruption this trace
    // column addressing must surface loudly instead of masking.
    u32::try_from(col)
        .unwrap_or_else(|_| panic!("column index {col} exceeds u32::MAX for layer-0 poly_idx"))
}

/// Walks the relation and returns `(output_address, field_type)` for every
/// poly the relation writes. Mirrors the relation-handling switch in
/// `forward.rs`: relations that emit base-typed polys (`LinearBaseFieldRelation`,
/// `MaterializeSingleLookupInput`, `CopyInBaseField`, `MaxQuadratic`) versus
/// extension-typed polys (everything else with outputs).
pub(super) fn relation_outputs<F: PrimeField>(
    rel: &NoFieldGKRRelation<F>,
) -> Vec<(GKRAddress, FieldType)> {
    use NoFieldGKRRelation::*;
    let mut out = Vec::new();
    match rel {
        LinearBaseFieldRelation { output, .. }
        | MaterializeSingleLookupInput { output, .. }
        | CopyInBaseField { output, .. }
        | MaxQuadratic { output, .. } => {
            out.push((*output, FieldType::Base));
        }
        EnforceSingleMaxQuadraticConstraint { .. } | EnforceConstraintsMaxQuadratic { .. } => {}
        CopyInExtensionField { output, .. }
        | InitialGrandProductFromCaches { output, .. }
        | InitialGrandProductWithoutCaches { output, .. }
        | UnbalancedGrandProductWithCache { output, .. }
        | MaterializeGrandProductTermExpression { output, .. }
        | TrivialProduct { output, .. }
        | MaskIntoIdentityProduct { output, .. }
        | MaterializedVectorLookupInput { output, .. }
        | InitsOrTeardownsInitialPair { output, .. } => {
            out.push((*output, FieldType::Ext));
        }
        LookupWithCachedDensAndSetup { output, .. }
        | LookupWithDensAndSetupExpressions { output, .. }
        | LookupPairFromBaseInputs { output, .. }
        | LookupPairFromMaterializedBaseInputs { output, .. }
        | LookupFromMaterializedBaseInputWithSetup { output, .. }
        | LookupUnbalancedPairWithMaterializedBaseInputs { output, .. }
        | LookupPairFromVectorInputs { output, .. }
        | LookupPairFromMaterializedVectorInputs { output, .. }
        | LookupPairFromCachedVectorInputs { output, .. }
        | LookupFromVectorInputWithSetup { output, .. }
        | LookupFromMaterializedVectorInputWithSetup { output, .. }
        | LookupUnbalancedPairWithVectorInputs { output, .. }
        | LookupUnbalancedPairWithMaterializedVectorInputs { output, .. }
        | AggregateLookupRationalPair { output, .. } => {
            for o in output.iter() {
                out.push((*o, FieldType::Ext));
            }
        }
    }
    out
}
