//! Per-launch builders that emit u16 source records into the compact
//! dim-reducing kernel-arg structs.
//!
//! Slot assignment is per-launch dynamic: each builder walks the addresses
//! for one batch, collects distinct `(backing_arc_pointer, log2_stride)` pairs
//! in order of first appearance, and packs each address as
//! `pack_source_u16(first_access, slot_idx, poly_idx)` against the resulting
//! tables.
//!
//! GPU scheduling contract: see gpu/docs/gpu_scheduling_contract.md. Builders run
//! on the scheduling thread, only read from `GpuGKRStorage` (no allocation,
//! no kernel launches), and emit a fully-baked descriptor that the launcher
//! ships to the device on `exec_stream`.

use std::collections::{BTreeMap, BTreeSet};

use super::super::storage_layout::address_storage_layer;
use super::super::GpuGKRStorage;
use super::kernels::FoldingArenaBinding;
use super::kernels::{
    pack_cache_u16, pack_source_u16, GpuGKRDimensionReducingBatch,
    GpuGKRDimensionReducingLayerSlots, GpuGKRDimensionReducingSlot, GpuGKRDimensionReducingTables,
    GpuGKRSourceRecord, GKR_DIM_REDUCING_BASE_SLOTS, GKR_DIM_REDUCING_IO_PER_SLOT,
};
use crate::upstream::{Field, GKRAddress};

/// Assign distinct backing pointers to source-table slots in first-use order.
struct SlotTableBuilder {
    bases: [*const u8; GKR_DIM_REDUCING_BASE_SLOTS],
    log2_stride: [u32; GKR_DIM_REDUCING_BASE_SLOTS],
    n_slots: usize,
    by_backing: BTreeMap<usize, usize>,
}

impl SlotTableBuilder {
    fn new() -> Self {
        Self {
            bases: [std::ptr::null(); GKR_DIM_REDUCING_BASE_SLOTS],
            log2_stride: [0; GKR_DIM_REDUCING_BASE_SLOTS],
            n_slots: 0,
            by_backing: BTreeMap::new(),
        }
    }

    /// Returns the slot index for `(backing_ptr, log2_stride)`, allocating a
    /// new slot if not yet seen. Panics on cap overflow.
    fn get_or_create(&mut self, backing_ptr: *const u8, log2_stride: u32) -> u8 {
        let key = backing_ptr as usize;
        if let Some(&slot) = self.by_backing.get(&key) {
            assert_eq!(
                self.log2_stride[slot], log2_stride,
                "slot table mismatch: backing {backing_ptr:?} reused with different log2_stride ({} vs {log2_stride})",
                self.log2_stride[slot]
            );
            return slot as u8;
        }
        assert!(
            self.n_slots < GKR_DIM_REDUCING_BASE_SLOTS,
            "exceeded GKR_DIM_REDUCING_BASE_SLOTS={GKR_DIM_REDUCING_BASE_SLOTS}; per-launch class fan-out above expected maximum",
        );
        let slot = self.n_slots;
        self.bases[slot] = backing_ptr;
        self.log2_stride[slot] = log2_stride;
        self.by_backing.insert(key, slot);
        self.n_slots += 1;
        slot as u8
    }

    fn into_tables(self) -> GpuGKRDimensionReducingTables {
        GpuGKRDimensionReducingTables {
            bases: self.bases,
            log2_stride: self.log2_stride,
        }
    }
}

/// `(layer, class)` lookup of an ext consolidated backing. Returns
/// `(backing_ptr, log2_stride, poly_idx)`.
fn resolve_ext_consolidated<B, E: Field>(
    storage: &GpuGKRStorage<B, E>,
    address: GKRAddress,
) -> (*const u8, u32, u16) {
    let layout = storage
        .layout
        .as_ref()
        .expect("storage layout required for compact dim-reducing encoding");
    let layer = address_storage_layer(address);
    let (canonical_layer, class, field, poly_idx) =
        layout.lookup(layer, &address).unwrap_or_else(|| {
            panic!("address {address:?} missing from storage layout at layer {layer}")
        });
    let layer_layout = layout.layers.get(canonical_layer).unwrap_or_else(|| {
        panic!("canonical layer {canonical_layer} out of range in layout for {address:?}")
    });
    assert!(
        matches!(field, crate::storage_layout::FieldType::Ext),
        "compact dim-reducing encoder expects ext-typed address; got {field:?} for {address:?}",
    );
    let backing = storage.layers[canonical_layer]
        .ext_class_backings
        .get(&class)
        .unwrap_or_else(|| {
            panic!(
                "ext_class_backings missing for layer {canonical_layer} class {class:?} (address {address:?}); GpuGKRStorage::allocate_ext_view should have allocated it"
            )
        });
    (
        backing.as_ptr() as *const u8,
        layer_layout.log2_stride,
        poly_idx as u16,
    )
}

fn folding_index<B, E>(
    storage: &GpuGKRStorage<B, E>,
    folding_addresses: &[GKRAddress],
    address: GKRAddress,
) -> u16 {
    let canonical = storage
        .layout
        .as_ref()
        .and_then(|layout| layout.aliases.get(&address))
        .copied()
        .unwrap_or(address);
    folding_addresses
        .binary_search(&canonical)
        .unwrap_or_else(|_| panic!("folding address {canonical:?} missing from dense arena"))
        .try_into()
        .expect("folding source index exceeds u16")
}

/// Step-1 descriptor: `src` names the original poly in consolidated ext storage,
/// where later steps name a prior folding arena. Both feed the same continuation
/// kernel.
pub(in crate::backward) fn build_round1_batch_compact_for_arena<B, E: Field>(
    layer_slots: &GpuGKRDimensionReducingLayerSlots,
    storage: &GpuGKRStorage<B, E>,
    folding_addresses: &[GKRAddress],
    destination: FoldingArenaBinding,
) -> GpuGKRDimensionReducingBatch<E> {
    let mut batch = GpuGKRDimensionReducingBatch::<E> {
        enabled_mask: layer_slots.enabled_mask(),
        ..Default::default()
    };
    let mut tables = SlotTableBuilder::new();
    let destination_slot = tables.get_or_create(destination.base, destination.log2_stride);
    let mut first_access_seen = BTreeSet::new();

    for (slot_idx, slot) in layer_slots.iter_enabled() {
        let mut io = [GpuGKRSourceRecord::default(); GKR_DIM_REDUCING_IO_PER_SLOT];
        for (k, address) in slot.inputs.iter().copied().enumerate() {
            let (input_ptr, input_stride, input_idx) = resolve_ext_consolidated(storage, address);
            let input_slot = tables.get_or_create(input_ptr, input_stride);
            let cache_idx = folding_index(storage, folding_addresses, address);
            let first_access = first_access_seen.insert(cache_idx);
            io[k] = GpuGKRSourceRecord::new(
                pack_source_u16(first_access, input_slot, input_idx),
                pack_cache_u16(destination_slot, cache_idx),
            );
        }
        batch.slots[slot_idx] = GpuGKRDimensionReducingSlot {
            io,
            batch_exp: slot.batch_exp,
        };
    }
    batch.tables = tables.into_tables();
    batch
}

pub(in crate::backward) fn build_continuation_batch_compact_for_arenas<B, E: Field>(
    layer_slots: &GpuGKRDimensionReducingLayerSlots,
    storage: &GpuGKRStorage<B, E>,
    folding_addresses: &[GKRAddress],
    current: FoldingArenaBinding,
    destination: FoldingArenaBinding,
) -> GpuGKRDimensionReducingBatch<E> {
    let mut batch = GpuGKRDimensionReducingBatch::<E> {
        enabled_mask: layer_slots.enabled_mask(),
        ..Default::default()
    };
    let mut tables = SlotTableBuilder::new();
    let current_slot = tables.get_or_create(current.base, current.log2_stride);
    let destination_slot = tables.get_or_create(destination.base, destination.log2_stride);
    let mut first_access_seen = BTreeSet::new();

    for (slot_idx, slot) in layer_slots.iter_enabled() {
        let mut io = [GpuGKRSourceRecord::default(); GKR_DIM_REDUCING_IO_PER_SLOT];
        for (k, address) in slot.inputs.iter().copied().enumerate() {
            let poly_idx = folding_index(storage, folding_addresses, address);
            let first_access = first_access_seen.insert(poly_idx);
            io[k] = GpuGKRSourceRecord::new(
                pack_source_u16(first_access, current_slot, poly_idx),
                pack_cache_u16(destination_slot, poly_idx),
            );
        }
        batch.slots[slot_idx] = GpuGKRDimensionReducingSlot {
            io,
            batch_exp: slot.batch_exp,
        };
    }
    batch.tables = tables.into_tables();
    batch
}

/// Build the round-0 batch descriptor. Both inputs and outputs resolve through
/// the consolidated `ext_class_backings`; the kernel uses
/// `gkr_resolve_dim_reducing_initial_source` which simply reads
/// `bases[ptr_idx] + (poly_idx << log2_stride[ptr_idx])`.
///
/// Returns the descriptor template with hot pointers (`eq_values`,
/// `contributions`) left null — the launcher fills these from the round
/// scratch.
pub(in crate::backward) fn build_round0_batch_compact<B, E: Field>(
    layer_slots: &GpuGKRDimensionReducingLayerSlots,
    storage: &GpuGKRStorage<B, E>,
) -> GpuGKRDimensionReducingBatch<E> {
    let mut batch = GpuGKRDimensionReducingBatch::<E> {
        enabled_mask: layer_slots.enabled_mask(),
        ..Default::default()
    };
    let mut tables = SlotTableBuilder::new();

    for (slot_idx, slot) in layer_slots.iter_enabled() {
        let mut io = [GpuGKRSourceRecord::default(); GKR_DIM_REDUCING_IO_PER_SLOT];
        let addresses = slot.inputs.iter().chain(slot.outputs.iter()).copied();
        for (k, address) in addresses.enumerate() {
            let (ptr, log2_stride, poly_idx) = resolve_ext_consolidated(storage, address);
            let table_slot = tables.get_or_create(ptr, log2_stride);
            io[k] = GpuGKRSourceRecord::source_only(pack_source_u16(false, table_slot, poly_idx));
        }
        batch.slots[slot_idx] = GpuGKRDimensionReducingSlot {
            io,
            batch_exp: slot.batch_exp,
        };
    }

    batch.tables = tables.into_tables();
    batch
}
