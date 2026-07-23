//! Core data types for the GKR storage layout: the `(slot, FieldType)`
//! storage key, the per-layer layout, and the per-circuit layout container.
//! Construction lives in [`super::construct`]; alias handling in
//! [`super::alias`]; dim-reducing tower layers in [`super::tower`].

use std::collections::{BTreeMap, BTreeSet};

use crate::address_audit::{AddressClass, GKR_MAX_POLYS_PER_SLOT, GKR_MAX_SLOTS};
use crate::upstream::GKRAddress;

use super::construct::address_storage_layer;

/// Field type a poly is stored as. Each `(layer, slot, FieldType)` triple gets
/// its own consolidated backing because base and extension polys have
/// different element strides.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FieldType {
    Base,
    Ext,
}

impl FieldType {
    pub(super) fn label(self) -> &'static str {
        match self {
            FieldType::Base => "base",
            FieldType::Ext => "ext",
        }
    }
}

/// `(slot, FieldType)` storage key. Each pair maps 1:1 to a consolidated
/// `Arc<DeviceAllocation>` at the storage layer.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StorageSlot {
    pub class: AddressClass,
    pub field: FieldType,
}

/// Per-layer storage layout: maps every poly that lives at this layer to a
/// `(slot, FieldType, poly_idx)` triple, plus the per-slot poly counts that
/// drive consolidated-backing sizing.
///
/// `log2_stride` is the per-poly stride for this layer — `log2(trace_len)`
/// for artifact layers (uniform across all artifact layers) and a decreasing
/// value for dim-reducing tower layers (each round halves the poly size).
#[derive(Debug, Clone, Default)]
pub struct GpuGKRLayerLayout {
    /// `GKRAddress -> (storage slot, field type, poly_idx within slot)`.
    pub index: BTreeMap<GKRAddress, (AddressClass, FieldType, u32)>,
    /// Poly count per `(slot, FieldType)`. Determines the size of the
    /// consolidated backing.
    pub slot_poly_counts: BTreeMap<StorageSlot, u32>,
    /// Per-poly stride at this layer; one poly occupies `1 << log2_stride`
    /// elements within its `(slot, FieldType)` consolidated backing.
    pub log2_stride: u32,
}

impl GpuGKRLayerLayout {
    pub fn lookup(&self, addr: &GKRAddress) -> Option<(AddressClass, FieldType, u32)> {
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
pub struct GpuGKRStorageLayout {
    /// `artifact.trace_len`. Kept here for diagnostics; allocators consult
    /// the per-layer `log2_stride` instead.
    pub trace_len: usize,
    /// `log2(artifact.trace_len)`. Same purpose as `trace_len` above.
    pub artifact_log2_stride: u32,
    pub layers: Vec<GpuGKRLayerLayout>,
    /// Alias -> canonical map for `CopyInBaseField` / `CopyInExtensionField`
    /// outputs. Aliases share their canonical's storage and do not claim
    /// their own slot in `index` / `slot_poly_counts`.
    pub aliases: BTreeMap<GKRAddress, GKRAddress>,
    /// `artifact.scratch_space_mapping_rev` (scratch slot -> logical
    /// `InnerLayer` address). Retained so the backward scheduler can recover a
    /// scratch-aliased value's logical protocol/claim identity via
    /// [`crate::transform::logical_protocol_address`]. See that function for
    /// why storage and protocol identity must diverge for scratch-backed
    /// values.
    pub scratch_space_mapping_rev: BTreeMap<usize, GKRAddress>,
}

impl GpuGKRStorageLayout {
    pub fn lookup(
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

    pub(super) fn assert_within_phase0_budgets(&self) {
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
