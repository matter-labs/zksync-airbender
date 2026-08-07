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
    pack_cache_u16, pack_source_u16, GpuGKRDimensionReducingBatchRecordCompact,
    GpuGKRDimensionReducingContinuationBatchCompact, GpuGKRDimensionReducingKernelPlan,
    GpuGKRDimensionReducingRound0BatchCompact, GpuGKRDimensionReducingTables, GpuGKRSourceRecord,
    PayloadRange16, GKR_DIM_REDUCING_BASE_SLOTS, GKR_DIM_REDUCING_INLINE_RECORD_CAP,
    GKR_DIM_REDUCING_MAX_INPUTS_PER_RECORD, GKR_DIM_REDUCING_MAX_OUTPUTS_PER_RECORD,
    GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER,
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

/// `PayloadRange16`.
fn push_payload_record(
    inline_payload: &mut [GpuGKRSourceRecord; GKR_DIM_REDUCING_INLINE_RECORD_CAP],
    cursor: &mut usize,
    value: GpuGKRSourceRecord,
) {
    assert!(
        *cursor < GKR_DIM_REDUCING_INLINE_RECORD_CAP,
        "compact dim-reducing inline_payload overflow at cursor {cursor} (cap {GKR_DIM_REDUCING_INLINE_RECORD_CAP})",
    );
    inline_payload[*cursor] = value;
    *cursor += 1;
}

fn check_record_count(blueprints_len: usize) {
    assert!(
        blueprints_len <= GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER,
        "compact dim-reducing encoder: {blueprints_len} blueprints exceeds GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER={GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER}",
    );
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

pub(in crate::backward) fn build_round1_batch_compact_for_arena<B, E: Field>(
    kernel_plans: &[GpuGKRDimensionReducingKernelPlan],
    storage: &GpuGKRStorage<B, E>,
    folding_addresses: &[GKRAddress],
    destination: FoldingArenaBinding,
) -> GpuGKRDimensionReducingContinuationBatchCompact<E> {
    check_record_count(kernel_plans.len());
    let mut batch = GpuGKRDimensionReducingContinuationBatchCompact::<E> {
        record_count: kernel_plans.len() as u32,
        ..Default::default()
    };
    let mut tables = SlotTableBuilder::new();
    let destination_slot = tables.get_or_create(destination.base, destination.log2_stride);
    let mut payload_cursor = 0usize;
    let mut first_access_seen = BTreeSet::new();

    for (idx, kernel) in kernel_plans.iter().enumerate() {
        let inputs_offset = payload_cursor as u16;
        let mut inputs_count = 0u16;
        for address in kernel.inputs.inputs_in_extension.iter().copied() {
            if address == GKRAddress::placeholder() {
                continue;
            }
            let (input_ptr, input_stride, input_idx) = resolve_ext_consolidated(storage, address);
            let input_slot = tables.get_or_create(input_ptr, input_stride);
            let cache_idx = folding_index(storage, folding_addresses, address);
            let first_access = first_access_seen.insert(cache_idx);
            push_payload_record(
                &mut batch.inline_payload,
                &mut payload_cursor,
                GpuGKRSourceRecord::new(
                    pack_source_u16(first_access, input_slot, input_idx),
                    pack_cache_u16(destination_slot, cache_idx),
                ),
            );
            inputs_count += 1;
        }
        assert!(usize::from(inputs_count) <= GKR_DIM_REDUCING_MAX_INPUTS_PER_RECORD);
        batch.records[idx] = GpuGKRDimensionReducingBatchRecordCompact {
            kind: kernel.kind.as_u32(),
            inputs: PayloadRange16 {
                offset: inputs_offset,
                count: inputs_count,
            },
            outputs: PayloadRange16::default(),
            batch_challenge_offset: kernel.batch_challenge_offset as u16,
            _reserved: 0,
        };
    }
    batch.tables = tables.into_tables();
    batch
}

pub(in crate::backward) fn build_continuation_batch_compact_for_arenas<B, E: Field>(
    kernel_plans: &[GpuGKRDimensionReducingKernelPlan],
    storage: &GpuGKRStorage<B, E>,
    folding_addresses: &[GKRAddress],
    current: FoldingArenaBinding,
    destination: FoldingArenaBinding,
) -> GpuGKRDimensionReducingContinuationBatchCompact<E> {
    check_record_count(kernel_plans.len());
    let mut batch = GpuGKRDimensionReducingContinuationBatchCompact::<E> {
        record_count: kernel_plans.len() as u32,
        ..Default::default()
    };
    let mut tables = SlotTableBuilder::new();
    let current_slot = tables.get_or_create(current.base, current.log2_stride);
    let destination_slot = tables.get_or_create(destination.base, destination.log2_stride);
    let mut payload_cursor = 0usize;
    let mut first_access_seen = BTreeSet::new();

    for (idx, kernel) in kernel_plans.iter().enumerate() {
        let inputs_offset = payload_cursor as u16;
        let mut inputs_count = 0u16;
        for address in kernel.inputs.inputs_in_extension.iter().copied() {
            if address == GKRAddress::placeholder() {
                continue;
            }
            let poly_idx = folding_index(storage, folding_addresses, address);
            let first_access = first_access_seen.insert(poly_idx);
            push_payload_record(
                &mut batch.inline_payload,
                &mut payload_cursor,
                GpuGKRSourceRecord::new(
                    pack_source_u16(first_access, current_slot, poly_idx),
                    pack_cache_u16(destination_slot, poly_idx),
                ),
            );
            inputs_count += 1;
        }
        assert!(usize::from(inputs_count) <= GKR_DIM_REDUCING_MAX_INPUTS_PER_RECORD);
        batch.records[idx] = GpuGKRDimensionReducingBatchRecordCompact {
            kind: kernel.kind.as_u32(),
            inputs: PayloadRange16 {
                offset: inputs_offset,
                count: inputs_count,
            },
            outputs: PayloadRange16::default(),
            batch_challenge_offset: kernel.batch_challenge_offset as u16,
            _reserved: 0,
        };
    }
    batch.tables = tables.into_tables();
    batch
}

/// Build the compact round-0 batch descriptor. Both inputs and outputs
/// resolve through the consolidated `ext_class_backings`; the kernel uses
/// `gkr_resolve_dim_reducing_initial_source` which simply reads
/// `bases[ptr_idx] + (poly_idx << log2_stride[ptr_idx])`.
///
/// Returns the descriptor template with hot pointers (`eq_values`,
/// `contributions`) left null — the launcher fills these from the round
/// scratch.
pub(in crate::backward) fn build_round0_batch_compact<B, E: Field>(
    blueprints: &[GpuGKRDimensionReducingKernelPlan],
    storage: &GpuGKRStorage<B, E>,
) -> GpuGKRDimensionReducingRound0BatchCompact<E> {
    check_record_count(blueprints.len());

    let mut batch = GpuGKRDimensionReducingRound0BatchCompact::<E> {
        record_count: blueprints.len() as u32,
        ..Default::default()
    };
    let mut tables = SlotTableBuilder::new();
    let mut payload_cursor = 0usize;

    for (idx, blueprint) in blueprints.iter().enumerate() {
        debug_assert!(blueprint.inputs.inputs_in_base.is_empty());
        debug_assert!(blueprint.inputs.outputs_in_base.is_empty());

        // Inputs.
        let inputs_offset = payload_cursor as u16;
        let mut inputs_count = 0u16;
        for addr in blueprint.inputs.inputs_in_extension.iter().copied() {
            if addr == GKRAddress::placeholder() {
                continue;
            }
            let (ptr, log2_stride, poly_idx) = resolve_ext_consolidated(storage, addr);
            let slot = tables.get_or_create(ptr, log2_stride);
            let packed = pack_source_u16(false, slot, poly_idx);
            push_payload_record(
                &mut batch.inline_payload,
                &mut payload_cursor,
                GpuGKRSourceRecord::source_only(packed),
            );
            inputs_count += 1;
        }
        assert!(usize::from(inputs_count) <= GKR_DIM_REDUCING_MAX_INPUTS_PER_RECORD);

        // Outputs.
        let outputs_offset = payload_cursor as u16;
        let mut outputs_count = 0u16;
        for addr in blueprint.inputs.outputs_in_extension.iter().copied() {
            if addr == GKRAddress::placeholder() {
                continue;
            }
            let (ptr, log2_stride, poly_idx) = resolve_ext_consolidated(storage, addr);
            let slot = tables.get_or_create(ptr, log2_stride);
            let packed = pack_source_u16(false, slot, poly_idx);
            push_payload_record(
                &mut batch.inline_payload,
                &mut payload_cursor,
                GpuGKRSourceRecord::source_only(packed),
            );
            outputs_count += 1;
        }
        assert!(usize::from(outputs_count) <= GKR_DIM_REDUCING_MAX_OUTPUTS_PER_RECORD);

        batch.records[idx] = GpuGKRDimensionReducingBatchRecordCompact {
            kind: blueprint.kind.as_u32(),
            inputs: PayloadRange16 {
                offset: inputs_offset,
                count: inputs_count,
            },
            outputs: PayloadRange16 {
                offset: outputs_offset,
                count: outputs_count,
            },
            batch_challenge_offset: blueprint.batch_challenge_offset as u16,
            _reserved: 0,
        };
    }

    batch.tables = tables.into_tables();
    batch
}
