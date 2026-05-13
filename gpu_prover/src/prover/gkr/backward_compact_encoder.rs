//! Per-launch builders that emit u16 source records into the compact
//! dim-reducing kernel-arg structs.
//!
//! Slot assignment is per-launch dynamic: each builder walks the addresses
//! for one batch, collects distinct `(backing_arc_pointer, log2_stride)` pairs
//! in order of first appearance, and packs each address as
//! `pack_source_u16(first_access, slot_idx, poly_idx)` against the resulting
//! tables.
//!
//! GPU scheduling contract: see docs/gpu_scheduling_contract.md. Builders run
//! on the scheduling thread, only read from `GpuGKRStorage` (no allocation,
//! no kernel launches), and emit a fully-baked descriptor that the launcher
//! ships to the device on `exec_stream`.

use std::collections::{BTreeMap, BTreeSet};

use cs::definitions::GKRAddress;
use field::Field;

use super::backward_kernels::{
    pack_cache_u16, pack_source_u16, DimensionReducingKernelBlueprint,
    GpuGKRDimensionReducingBatchRecordCompact, GpuGKRDimensionReducingContinuationBatchCompact,
    GpuGKRDimensionReducingRound0BatchCompact, GpuGKRDimensionReducingTables, GpuGKRSourceRecord,
    PayloadRange16, GKR_DIM_REDUCING_BASE_SLOTS, GKR_DIM_REDUCING_INLINE_U16_BUDGET,
    GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER,
};
use super::storage_layout::address_storage_layer;
use super::GpuGKRStorage;

/// Per-launch slot assignment helper. Maps distinct `(backing_arc_pointer,
/// log2_stride)` pairs to slot indices in first-appearance order, panicking
/// past `GKR_DIM_REDUCING_BASE_SLOTS = 16` (sized to fit main-layer
/// flat-path round 1/2 launches that touch up to ~10 distinct backings).
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
        matches!(field, super::storage_layout::FieldType::Ext),
        "compact dim-reducing encoder expects ext-typed address; got {field:?} for {address:?}",
    );
    let backing = storage.layers[canonical_layer]
        .ext_class_backings
        .get(&class)
        .unwrap_or_else(|| {
            panic!(
                "ext_class_backings missing for layer {canonical_layer} class {class:?} (address {address:?}); register_dim_reducing_inputs_for_layer should have allocated it"
            )
        });
    let resolved = unsafe {
        (backing.as_ptr() as *const E).add((poly_idx as usize) << layer_layout.log2_stride)
    };
    let legacy = storage
        .try_get_ext_poly(address)
        .map(|p| p.as_ptr())
        .unwrap_or(std::ptr::null());
    debug_assert_eq!(
        resolved, legacy,
        "compact ext-resolve {address:?} -> {resolved:?} mismatches legacy view {legacy:?} (layer {canonical_layer}, class {class:?}, poly_idx {poly_idx}, log2_stride {})",
        layer_layout.log2_stride,
    );
    (
        backing.as_ptr() as *const u8,
        layer_layout.log2_stride,
        poly_idx as u16,
    )
}

/// `(layer, class)` lookup of the matching folding-buffer backing. Returns
/// `(backing_ptr, log2_stride, poly_idx)`. The folding-buffer log2_stride is
/// `log2(per_poly_size)`; the poly_idx aligns with the matching
/// `ext_class_backing`.
fn resolve_ext_folding_buffer<B, E: Field>(
    storage: &GpuGKRStorage<B, E>,
    address: GKRAddress,
) -> (*const u8, u32, u16) {
    let layout = storage
        .layout
        .as_ref()
        .expect("storage layout required for compact dim-reducing encoding");
    let layer = address_storage_layer(address);
    let (_canonical_layer, class, _field, _poly_idx) =
        layout.lookup(layer, &address).unwrap_or_else(|| {
            panic!("address {address:?} missing from storage layout at layer {layer}")
        });
    let consolidated = storage.layers[layer]
        .intermediate_folding_consolidated
        .as_ref()
        .unwrap_or_else(|| {
            panic!(
                "intermediate_folding_consolidated missing for layer {layer}; register_dim_reducing_inputs_for_layer should have allocated it"
            )
        });
    let backing = consolidated.per_class.get(&class).unwrap_or_else(|| {
        panic!(
            "intermediate_folding_consolidated.per_class[{class:?}] missing at layer {layer} for address {address:?}",
        )
    });
    let cache_poly_idx = consolidated.poly_index.get(&address).copied().unwrap_or_else(|| {
        panic!("intermediate_folding_consolidated missing dense cache index for {address:?} at layer {layer}")
    });
    let log2_stride = (consolidated.per_poly_size as u32).trailing_zeros();
    debug_assert_eq!(
        1usize << log2_stride,
        consolidated.per_poly_size,
        "consolidated folding per_poly_size must be a power of two",
    );
    (backing.as_ptr() as *const u8, log2_stride, cache_poly_idx)
}

/// Push a u16 onto the inline payload, bumping the write cursor and panicking
/// on overflow. `cursor` is the `(offset, count)` builder for the current
/// `PayloadRange16`.
fn push_payload_record(
    inline_payload: &mut [GpuGKRSourceRecord; GKR_DIM_REDUCING_INLINE_U16_BUDGET],
    cursor: &mut usize,
    value: GpuGKRSourceRecord,
) {
    assert!(
        *cursor < GKR_DIM_REDUCING_INLINE_U16_BUDGET,
        "compact dim-reducing inline_payload overflow at cursor {cursor} (budget {GKR_DIM_REDUCING_INLINE_U16_BUDGET})",
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

/// Build the compact round-0 batch descriptor. Both inputs and outputs
/// resolve through the consolidated `ext_class_backings`; the kernel uses
/// `gkr_resolve_dim_reducing_initial_source` which simply reads
/// `bases[ptr_idx] + (poly_idx << log2_stride[ptr_idx])`.
///
/// Returns the descriptor template with hot pointers (`eq_values`,
/// `contributions`) left null — the launcher fills these from the round
/// scratch.
pub(super) fn build_round0_batch_compact<B, E: Field>(
    blueprints: &[DimensionReducingKernelBlueprint<E>],
    storage: &GpuGKRStorage<B, E>,
) -> GpuGKRDimensionReducingRound0BatchCompact<E> {
    check_record_count(blueprints.len());

    let mut batch = GpuGKRDimensionReducingRound0BatchCompact::<E>::default();
    batch.record_count = blueprints.len() as u32;
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
            batch_challenge_count: blueprint.batch_challenge_count as u16,
        };
    }

    batch.tables = tables.into_tables();
    batch
}

/// Build the compact round-1 batch descriptor. For each ext input poly, the
/// encoder collects (a) the original ext input slot in `ext_class_backings`,
/// (b) the matching folding-buffer slot in
/// `intermediate_folding_consolidated`. The kernel reads `previous_layer_start`
/// from the input slot and `this_layer_start` from
/// the record's cache half. The source and cache poly_idx values may differ
/// for copy aliases.
///
/// `first_access` follows `last_used_for_layer` semantics: the first
/// occurrence of a given `(layer, address)` pair within the batch payload
/// returns `true`, subsequent occurrences return `false`.
pub(super) fn build_round1_batch_compact<B, E: Field>(
    blueprints: &[DimensionReducingKernelBlueprint<E>],
    storage: &GpuGKRStorage<B, E>,
) -> GpuGKRDimensionReducingContinuationBatchCompact<E> {
    check_record_count(blueprints.len());

    let mut batch = GpuGKRDimensionReducingContinuationBatchCompact::<E>::default();
    batch.record_count = blueprints.len() as u32;
    let mut tables = SlotTableBuilder::new();
    let mut payload_cursor = 0usize;
    let mut first_access_seen: BTreeSet<(usize, GKRAddress)> = BTreeSet::new();

    for (idx, blueprint) in blueprints.iter().enumerate() {
        debug_assert!(blueprint.inputs.inputs_in_base.is_empty());

        let inputs_offset = payload_cursor as u16;
        let mut inputs_count = 0u16;
        for addr in blueprint.inputs.inputs_in_extension.iter().copied() {
            if addr == GKRAddress::placeholder() {
                continue;
            }
            let (input_ptr, input_log2_stride, poly_idx) = resolve_ext_consolidated(storage, addr);
            let (folding_ptr, folding_log2_stride, folding_poly_idx) =
                resolve_ext_folding_buffer(storage, addr);
            let input_slot = tables.get_or_create(input_ptr, input_log2_stride);
            let folding_slot = tables.get_or_create(folding_ptr, folding_log2_stride);

            let layer = address_storage_layer(addr);
            let key = (layer, addr);
            let first_access = first_access_seen.insert(key);
            let src = pack_source_u16(first_access, input_slot, poly_idx);
            let cache = pack_cache_u16(folding_slot, folding_poly_idx);
            push_payload_record(
                &mut batch.inline_payload,
                &mut payload_cursor,
                GpuGKRSourceRecord::new(src, cache),
            );
            inputs_count += 1;
        }

        batch.records[idx] = GpuGKRDimensionReducingBatchRecordCompact {
            kind: blueprint.kind.as_u32(),
            inputs: PayloadRange16 {
                offset: inputs_offset,
                count: inputs_count,
            },
            outputs: PayloadRange16::default(),
            batch_challenge_offset: blueprint.batch_challenge_offset as u16,
            batch_challenge_count: blueprint.batch_challenge_count as u16,
        };
    }

    batch.tables = tables.into_tables();
    batch
}

/// Build the compact continuation batch descriptor for sumcheck steps >= 2.
/// Sources resolve through folding-buffer slots only; the kernel uses
/// `gkr_resolve_dim_reducing_continuation_source` which derives per-step
/// offsets from `step + acc_size`.
///
/// `first_access` is `true` on the first occurrence of a
/// `(layer, address)` pair within this step's batch payload.
pub(super) fn build_continuation_batch_compact<B, E: Field>(
    blueprints: &[DimensionReducingKernelBlueprint<E>],
    storage: &GpuGKRStorage<B, E>,
) -> GpuGKRDimensionReducingContinuationBatchCompact<E> {
    check_record_count(blueprints.len());

    let mut batch = GpuGKRDimensionReducingContinuationBatchCompact::<E>::default();
    batch.record_count = blueprints.len() as u32;
    let mut tables = SlotTableBuilder::new();
    let mut payload_cursor = 0usize;
    let mut first_access_seen: BTreeSet<(usize, GKRAddress)> = BTreeSet::new();

    for (idx, blueprint) in blueprints.iter().enumerate() {
        debug_assert!(blueprint.inputs.inputs_in_base.is_empty());

        let inputs_offset = payload_cursor as u16;
        let mut inputs_count = 0u16;
        for addr in blueprint.inputs.inputs_in_extension.iter().copied() {
            if addr == GKRAddress::placeholder() {
                continue;
            }
            let (folding_ptr, folding_log2_stride, poly_idx) =
                resolve_ext_folding_buffer(storage, addr);
            let folding_slot = tables.get_or_create(folding_ptr, folding_log2_stride);

            let layer = address_storage_layer(addr);
            let key = (layer, addr);
            let first_access = first_access_seen.insert(key);
            let src = pack_source_u16(first_access, folding_slot, poly_idx);
            let cache = pack_cache_u16(folding_slot, poly_idx);
            push_payload_record(
                &mut batch.inline_payload,
                &mut payload_cursor,
                GpuGKRSourceRecord::new(src, cache),
            );
            inputs_count += 1;
        }

        batch.records[idx] = GpuGKRDimensionReducingBatchRecordCompact {
            kind: blueprint.kind.as_u32(),
            inputs: PayloadRange16 {
                offset: inputs_offset,
                count: inputs_count,
            },
            outputs: PayloadRange16::default(),
            batch_challenge_offset: blueprint.batch_challenge_offset as u16,
            batch_challenge_count: blueprint.batch_challenge_count as u16,
        };
    }

    batch.tables = tables.into_tables();
    batch
}
