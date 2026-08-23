// Task 4 consumes the R0 binder; D1/DR-cont consumes the shared arena path.
#![allow(dead_code)]

use std::collections::BTreeMap;
use std::sync::Arc;

use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::E4;

use crate::backward::kernels::{
    pack_source_u16, FoldingArenaBinding, GpuGKRDimensionReducingTables,
    GKR_DIM_REDUCING_BASE_SLOTS, GKR_DIM_REDUCING_POLY_CAPACITY,
};
use crate::gkr_address_audit::AddressClass;
use crate::storage_layout::{address_storage_layer, FieldType};
use crate::upstream::GKRAddress;
use crate::GpuGKRStorage;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum DrWindowBindError {
    MissingStorageLayout {
        address: GKRAddress,
    },
    MissingSource {
        address: GKRAddress,
        logical_layer: usize,
    },
    NonE4Source {
        address: GKRAddress,
        field: FieldType,
    },
    MissingE4Backing {
        address: GKRAddress,
        canonical_layer: usize,
        class: AddressClass,
    },
    StrideMismatch {
        backing: usize,
        expected_log2_stride: u32,
        observed_log2_stride: u32,
    },
    BaseSlotOverflow {
        required: usize,
        capacity: usize,
    },
    PolyIndexOverflow {
        poly_index: usize,
        capacity: usize,
    },
}

impl core::fmt::Display for DrWindowBindError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for DrWindowBindError {}

pub(super) struct ResolvedStorageE4<'a> {
    pub(super) backing: &'a Arc<DeviceAllocation<E4>>,
    pub(super) log2_stride: u32,
    pub(super) poly_index: usize,
}

pub(super) fn resolve_storage_e4<'a, B>(
    storage: &'a GpuGKRStorage<B, E4>,
    address: GKRAddress,
) -> Result<ResolvedStorageE4<'a>, DrWindowBindError> {
    let layout = storage
        .layout
        .as_ref()
        .ok_or(DrWindowBindError::MissingStorageLayout { address })?;
    let logical_layer = address_storage_layer(address);
    let (canonical_layer, class, field, poly_index) = layout
        .lookup(logical_layer, &address)
        .ok_or(DrWindowBindError::MissingSource {
            address,
            logical_layer,
        })?;
    if field != FieldType::Ext {
        return Err(DrWindowBindError::NonE4Source { address, field });
    }
    let layer_layout =
        layout
            .layers
            .get(canonical_layer)
            .ok_or(DrWindowBindError::MissingE4Backing {
                address,
                canonical_layer,
                class,
            })?;
    let layer = storage
        .layers
        .get(canonical_layer)
        .ok_or(DrWindowBindError::MissingE4Backing {
            address,
            canonical_layer,
            class,
        })?;
    let backing =
        layer
            .ext_class_backings
            .get(&class)
            .ok_or(DrWindowBindError::MissingE4Backing {
                address,
                canonical_layer,
                class,
            })?;
    Ok(ResolvedStorageE4 {
        backing,
        log2_stride: layer_layout.log2_stride,
        poly_index: poly_index as usize,
    })
}

/// Per-launch compact pointer table shared by DR R0 and its continuations.
/// Backing slots are assigned in order of first use.
pub(crate) struct DrCompactSourceTableBuilder {
    tables: GpuGKRDimensionReducingTables,
    by_backing: BTreeMap<usize, usize>,
    slot_count: usize,
}

impl DrCompactSourceTableBuilder {
    pub(crate) fn new() -> Self {
        Self {
            tables: GpuGKRDimensionReducingTables::default(),
            by_backing: BTreeMap::new(),
            slot_count: 0,
        }
    }

    /// Returns the bit-15-clear slot/poly wire base for an E4 storage source.
    /// Task 4 uses this directly for R0. D1/DR-cont record assembly owns the
    /// first-access bit and must OR bit 15 onto this base after per-launch
    /// canonical-folding-index dedup, without rederiving the slot or poly.
    pub(crate) fn intern_storage_e4<B>(
        &mut self,
        storage: &GpuGKRStorage<B, E4>,
        address: GKRAddress,
    ) -> Result<u16, DrWindowBindError> {
        let resolved = resolve_storage_e4(storage, address)?;
        self.intern_resolved(
            resolved.backing.as_ptr().cast(),
            resolved.log2_stride,
            resolved.poly_index,
        )
    }

    /// Returns the bit-15-clear slot/poly wire base for an E4 folding arena.
    /// D1/DR-cont record assembly owns the first-access bit and must OR bit 15
    /// onto this base after per-launch canonical-folding-index dedup, without
    /// rederiving the slot or poly.
    pub(crate) fn intern_arena_e4(
        &mut self,
        arena: FoldingArenaBinding,
        poly_index: usize,
    ) -> Result<u16, DrWindowBindError> {
        self.intern_resolved(arena.base, arena.log2_stride, poly_index)
    }

    pub(crate) fn finish(self) -> GpuGKRDimensionReducingTables {
        self.tables
    }

    fn intern_resolved(
        &mut self,
        backing: *const u8,
        log2_stride: u32,
        poly_index: usize,
    ) -> Result<u16, DrWindowBindError> {
        if poly_index >= GKR_DIM_REDUCING_POLY_CAPACITY {
            return Err(DrWindowBindError::PolyIndexOverflow {
                poly_index,
                capacity: GKR_DIM_REDUCING_POLY_CAPACITY,
            });
        }

        let backing_key = backing as usize;
        let slot = if let Some(&slot) = self.by_backing.get(&backing_key) {
            let expected_log2_stride = self.tables.log2_stride[slot];
            if expected_log2_stride != log2_stride {
                return Err(DrWindowBindError::StrideMismatch {
                    backing: backing_key,
                    expected_log2_stride,
                    observed_log2_stride: log2_stride,
                });
            }
            slot
        } else {
            if self.slot_count == GKR_DIM_REDUCING_BASE_SLOTS {
                return Err(DrWindowBindError::BaseSlotOverflow {
                    required: self.slot_count + 1,
                    capacity: GKR_DIM_REDUCING_BASE_SLOTS,
                });
            }
            let slot = self.slot_count;
            self.tables.bases[slot] = backing;
            self.tables.log2_stride[slot] = log2_stride;
            self.by_backing.insert(backing_key, slot);
            self.slot_count += 1;
            slot
        };

        Ok(pack_source_u16(false, slot as u8, poly_index as u16))
    }
}

impl Default for DrCompactSourceTableBuilder {
    fn default() -> Self {
        Self::new()
    }
}
