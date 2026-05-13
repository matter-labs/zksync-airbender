//! CPU-only storage layout for the GKR backward path.
//!
//! Walks a `cs::gkr_compiler::GKRCircuitArtifact` and produces, per storage
//! layer, a deterministic `(slot, FieldType, poly_idx)` mapping for every
//! `GKRAddress` that has a poly *living* at that layer. The 8-slot taxonomy
//! is shared with `gkr_address_audit`:
//!
//! - slots 0..2 are layer-0 read sources (BaseLayerWitness, BaseLayerMemory,
//!   Setup + VirtualSetup) and are externally backed by trace holders.
//! - slots 5..6 are this-layer write targets (Cached and InnerLayer) and are
//!   the freshly-allocated consolidated backings the storage refactor will
//!   target.
//! - slot 7 is layer-0 ScratchSpace, externally backed by `stage1`.
//! - slots 3..4 are kernel-side aliases for prev-layer slots 5/6 — never
//!   populated in the storage layout.
//!
//! The layout is the data structure every compact-`u16` descriptor builder
//! consults to encode `(ptr_idx, poly_idx)` against the per-launch pointer
//! table.

use std::collections::{BTreeMap, BTreeSet};

use cs::definitions::GKRAddress;
use cs::gkr_compiler::{
    GKRCircuitArtifact, NoFieldGKRCacheRelation, NoFieldGKRRelation, OutputType,
};
use field::PrimeField;

use super::gkr_address_audit::{
    classify, collect_addresses_from_cache_relation, collect_addresses_from_relation, AddressClass,
    GKR_MAX_POLYS_PER_SLOT, GKR_MAX_SLOTS,
};

/// Field type a poly is stored as. Each `(layer, slot, FieldType)` triple gets
/// its own consolidated backing because base and extension polys have
/// different element strides.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum FieldType {
    Base,
    Ext,
}

impl FieldType {
    fn label(self) -> &'static str {
        match self {
            FieldType::Base => "base",
            FieldType::Ext => "ext",
        }
    }
}

/// `(slot, FieldType)` storage key. Each pair maps 1:1 to a consolidated
/// `Arc<DeviceAllocation>` at the storage layer.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct StorageSlot {
    pub(crate) class: AddressClass,
    pub(crate) field: FieldType,
}

/// Per-layer storage layout: maps every poly that lives at this layer to a
/// `(slot, FieldType, poly_idx)` triple, plus the per-slot poly counts that
/// drive consolidated-backing sizing.
///
/// `log2_stride` is the per-poly stride for this layer — `log2(trace_len)`
/// for artifact layers (uniform across all artifact layers) and a decreasing
/// value for dim-reducing tower layers (each round halves the poly size).
#[derive(Debug, Clone, Default)]
pub(crate) struct GpuGKRLayerLayout {
    /// `GKRAddress -> (storage slot, field type, poly_idx within slot)`.
    pub(crate) index: BTreeMap<GKRAddress, (AddressClass, FieldType, u32)>,
    /// Poly count per `(slot, FieldType)`. Determines the size of the
    /// consolidated backing the storage refactor will allocate.
    pub(crate) slot_poly_counts: BTreeMap<StorageSlot, u32>,
    /// Per-poly stride at this layer; one poly occupies `1 << log2_stride`
    /// elements within its `(slot, FieldType)` consolidated backing.
    pub(crate) log2_stride: u32,
}

impl GpuGKRLayerLayout {
    pub(crate) fn lookup(&self, addr: &GKRAddress) -> Option<(AddressClass, FieldType, u32)> {
        self.index.get(addr).copied()
    }
}

/// Per-circuit storage layout: one `GpuGKRLayerLayout` per layer. Artifact
/// layers (the prefix indexed `0..artifact.layers.len()+1`) all share
/// `artifact_log2_stride = log2(trace_len)`; dim-reducing tower layers
/// (appended past the artifact range when constructed via
/// [`Self::from_artifact_with_tower`]) carry decreasing strides via each
/// `GpuGKRLayerLayout::log2_stride`.
#[derive(Debug, Clone)]
pub(crate) struct GpuGKRStorageLayout {
    /// `artifact.trace_len`. Kept here for diagnostics; allocators consult
    /// the per-layer `log2_stride` instead.
    #[allow(dead_code)]
    pub(crate) trace_len: usize,
    /// `log2(artifact.trace_len)`. Same purpose as `trace_len` above.
    #[allow(dead_code)]
    pub(crate) artifact_log2_stride: u32,
    pub(crate) layers: Vec<GpuGKRLayerLayout>,
    /// Alias -> canonical map for `CopyInBaseField` / `CopyInExtensionField`
    /// outputs. Aliases share their canonical's storage and do not claim
    /// their own slot in `index` / `slot_poly_counts`.
    pub(crate) aliases: BTreeMap<GKRAddress, GKRAddress>,
}

impl GpuGKRStorageLayout {
    /// Build the layout from artifact gates only. Tower-layer entries are
    /// **not** included; allocators will panic on tower-layer addresses.
    /// Use [`Self::from_artifact_with_tower`] for the production path.
    #[cfg(test)]
    pub(crate) fn from_artifact<F: PrimeField>(artifact: &GKRCircuitArtifact<F>) -> Self {
        Self::from_artifact_inner(artifact, None)
    }

    /// Build the layout from artifact gates and append tower-layer entries
    /// for the dim-reducing forward chain. Each tower layer carries its own
    /// `log2_stride` (halving each round, starting from
    /// `log2(trace_len) - 1`).
    pub(crate) fn from_artifact_with_tower<F: PrimeField>(
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
        };
        layout.assert_within_phase0_budgets();
        layout.assert_aliases_resolve();
        layout
    }

    fn assert_aliases_resolve(&self) {
        for (alias, canonical) in self.aliases.iter() {
            assert!(
                !self.aliases.contains_key(canonical),
                "alias chain not fully compressed: {alias:?} -> {canonical:?}",
            );
            let canonical_layer = address_storage_layer(*canonical);
            let layer_layout = self.layers.get(canonical_layer).unwrap_or_else(|| {
                panic!(
                    "alias {alias:?} resolves to canonical {canonical:?} at layer {canonical_layer}, out of range ({} layers)",
                    self.layers.len(),
                )
            });
            assert!(
                layer_layout.index.contains_key(canonical),
                "alias {alias:?} resolves to canonical {canonical:?} missing from layer {canonical_layer}'s index",
            );
        }
    }

    pub(crate) fn lookup(
        &self,
        layer: usize,
        addr: &GKRAddress,
    ) -> Option<(usize, AddressClass, FieldType, u32)> {
        if let Some(layer_layout) = self.layers.get(layer) {
            if let Some((class, field, poly_idx)) = layer_layout.lookup(addr) {
                return Some((layer, class, field, poly_idx));
            }
        }
        // Same-address fallback at the canonical storage layer. Covers
        // base-field addresses (e.g., `ScratchSpace(K)` at layer 0)
        // whose value lives at `address_storage_layer(addr)` but is
        // looked up via a higher logical `layer` — common after
        // `normalize_compiled_circuit_for_gpu` rewrites
        // `InnerLayer { layer: L, .. }` into `ScratchSpace(K)` (layer 0)
        // for kernels at layer L.
        let same_addr_canonical = address_storage_layer(*addr);
        if same_addr_canonical != layer {
            if let Some(layer_layout) = self.layers.get(same_addr_canonical) {
                if let Some((class, field, poly_idx)) = layer_layout.lookup(addr) {
                    return Some((same_addr_canonical, class, field, poly_idx));
                }
            }
        }
        // Alias fallback for `CopyIn{Base,Extension}Field` outputs.
        let canonical = self.aliases.get(addr)?;
        let canonical_layer = address_storage_layer(*canonical);
        let layer_layout = self.layers.get(canonical_layer)?;
        let (class, field, poly_idx) = layer_layout.lookup(canonical)?;
        Some((canonical_layer, class, field, poly_idx))
    }

    fn assert_within_phase0_budgets(&self) {
        for (layer_idx, layer) in self.layers.iter().enumerate() {
            for (slot, count) in layer.slot_poly_counts.iter() {
                assert!(
                    *count as usize <= GKR_MAX_POLYS_PER_SLOT,
                    "layer {layer_idx} slot {:?}/{} has {} polys, exceeds GKR_MAX_POLYS_PER_SLOT={}",
                    slot.class,
                    slot.field.label(),
                    count,
                    GKR_MAX_POLYS_PER_SLOT
                );
            }
            let distinct_classes: BTreeSet<AddressClass> =
                layer.slot_poly_counts.keys().map(|s| s.class).collect();
            assert!(
                distinct_classes.len() <= GKR_MAX_SLOTS,
                "layer {layer_idx} uses {} address classes, exceeds GKR_MAX_SLOTS={}",
                distinct_classes.len(),
                GKR_MAX_SLOTS
            );
        }
    }
}

/// Returns the storage layer at which a poly with this address lives:
/// `0` for trace-holder-backed and scratch-space addresses, and the address's
/// `layer` field for `InnerLayer` / `Cached`.
pub(crate) fn address_storage_layer(addr: GKRAddress) -> usize {
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

/// Append per-tower-layer `GpuGKRLayerLayout` entries to `layers`, mirroring
/// the address derivation in
/// `crate::prover::gkr::backward::derive_dimension_reducing_inputs_structural`
/// and the output assignment in
/// `crate::prover::gkr::forward::lower_dimension_reducing_forward_round`.
///
/// Tower layer N (relative to the artifact's last storage layer) holds polys
/// of size `1 << (initial_trace_log_2 - 1 - N)` (one halving per round).
/// All tower outputs are extension-field `InnerLayer { layer, offset }` with
/// `AddressClass::ThisLayerInnerLayerWrite` (since `addr.layer == output_layer`
/// in `classify`'s sense). Sequential `offset` per layer maps directly to
/// `poly_idx`.
fn append_tower_layers<F: PrimeField>(
    layers: &mut Vec<GpuGKRLayerLayout>,
    artifact: &GKRCircuitArtifact<F>,
    initial_trace_log_2: usize,
    final_trace_log_2: usize,
) {
    let total_rounds = initial_trace_log_2.saturating_sub(final_trace_log_2);
    if total_rounds == 0 {
        return;
    }
    // Tower starts one storage layer past the artifact's last input layer.
    // `schedule_dimension_reduction_forward` is called with
    // `initial_layer_idx = compiled_circuit.layers.len()` and writes round 0's
    // outputs at `output_layer = initial_layer_idx + 1`. The artifact-driven
    // layout already covers up to `compiled_circuit.layers.len()`, so the
    // first new layer to allocate is `compiled_circuit.layers.len() + 1`.
    let initial_layer_idx = artifact.layers.len();

    let mut layer_inputs: BTreeMap<OutputType, Vec<GKRAddress>> =
        artifact.global_output_map.clone();
    let mut current_layer_idx = initial_layer_idx;
    for round in 0..total_rounds {
        let output_layer = current_layer_idx + 1;
        let input_size_log_2 = initial_trace_log_2 - round;
        let output_log2_stride = (input_size_log_2 - 1) as u32;

        let mut new_layer_layout = GpuGKRLayerLayout {
            log2_stride: output_log2_stride,
            ..GpuGKRLayerLayout::default()
        };
        let mut output_idx: u32 = 0;
        let mut next_inputs: BTreeMap<OutputType, Vec<GKRAddress>> = BTreeMap::new();

        for (arg_type, inputs) in layer_inputs.iter() {
            assert_eq!(
                inputs.len(),
                2,
                "dim reduction tower expects 2 inputs per slot for {:?}",
                arg_type,
            );
            let out_a = GKRAddress::InnerLayer {
                layer: output_layer,
                offset: output_idx as usize,
            };
            let poly_idx_a = output_idx;
            output_idx += 1;
            let out_b = GKRAddress::InnerLayer {
                layer: output_layer,
                offset: output_idx as usize,
            };
            let poly_idx_b = output_idx;
            output_idx += 1;

            let class = AddressClass::ThisLayerInnerLayerWrite;
            let field = FieldType::Ext;
            new_layer_layout
                .index
                .insert(out_a, (class, field, poly_idx_a));
            new_layer_layout
                .index
                .insert(out_b, (class, field, poly_idx_b));
            next_inputs.insert(*arg_type, vec![out_a, out_b]);
        }
        if output_idx > 0 {
            new_layer_layout.slot_poly_counts.insert(
                StorageSlot {
                    class: AddressClass::ThisLayerInnerLayerWrite,
                    field: FieldType::Ext,
                },
                output_idx,
            );
        }

        // Resize layers vector to cover `output_layer`. The tower layout's
        // `log2_stride` carries the round-specific size — earlier (artifact)
        // strides do not apply to these fresh per-round outputs.
        if output_layer >= layers.len() {
            layers.resize_with(output_layer + 1, GpuGKRLayerLayout::default);
        }
        layers[output_layer] = new_layer_layout;

        layer_inputs = next_inputs;
        current_layer_idx += 1;
    }
}

fn build_alias_redirects<F: PrimeField>(
    artifact: &GKRCircuitArtifact<F>,
) -> BTreeMap<GKRAddress, GKRAddress> {
    use cs::gkr_compiler::NoFieldGKRRelation;

    fn find(parent: &mut BTreeMap<GKRAddress, GKRAddress>, addr: GKRAddress) -> GKRAddress {
        let p = parent.get(&addr).copied().unwrap_or(addr);
        if p == addr {
            return addr;
        }
        let root = find(parent, p);
        parent.insert(addr, root);
        root
    }

    let mut parent: BTreeMap<GKRAddress, GKRAddress> = BTreeMap::new();
    for layer in artifact.layers.iter() {
        for gate in layer
            .gates
            .iter()
            .chain(layer.gates_with_external_connections.iter())
        {
            match &gate.enforced_relation {
                NoFieldGKRRelation::CopyInBaseField { input, output }
                | NoFieldGKRRelation::CopyInExtensionField { input, output } => {
                    let root = find(&mut parent, *input);
                    parent.insert(*output, root);
                }
                _ => {}
            }
        }
    }
    let alias_keys: Vec<_> = parent.keys().copied().collect();
    for addr in alias_keys {
        find(&mut parent, addr);
    }
    parent
        .into_iter()
        .filter(|(alias, canonical)| alias != canonical)
        .collect()
}

fn cache_relation_output_type(rel: &NoFieldGKRCacheRelation) -> FieldType {
    use NoFieldGKRCacheRelation::*;
    match rel {
        SingleColumnLookup { .. } => FieldType::Base,
        VectorizedLookup(_) | VectorizedLookupSetup(_) | MemoryTuple(_) => FieldType::Ext,
    }
}

fn column_index_for_layer0(addr: &GKRAddress) -> u32 {
    match addr {
        GKRAddress::BaseLayerWitness(col)
        | GKRAddress::BaseLayerMemory(col)
        | GKRAddress::Setup(col)
        | GKRAddress::ScratchSpace(col) => *col as u32,
        _ => unreachable!(
            "column_index_for_layer0 called on non-trace-holder address {:?}",
            addr
        ),
    }
}

/// Walks the relation and returns `(output_address, field_type)` for every
/// poly the relation writes. Mirrors the relation-handling switch in
/// `forward.rs`: relations that emit base-typed polys (`LinearBaseFieldRelation`,
/// `MaterializeSingleLookupInput`, `CopyInBaseField`, `MaxQuadratic`) versus
/// extension-typed polys (everything else with outputs).
fn relation_outputs(rel: &NoFieldGKRRelation) -> Vec<(GKRAddress, FieldType)> {
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

#[cfg(test)]
mod tests;
