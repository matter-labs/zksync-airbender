use super::binding::DrWindowBindError;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use gpu_core::primitives::context::DeviceAllocation;
use gpu_gkr_compiler::{DrWindowInputProjection, DrWindowProgram};

use crate::backward::{
    pack_source_u16, FoldingArenaBinding, GkrEqSizes, GpuGKRDimensionReducingBatch,
    GpuGKRDimensionReducingSlot, GpuGKRDimensionReducingTables, GpuGKRSourceRecord,
    GKR_DIM_REDUCING_BASE_SLOTS, GKR_DIM_REDUCING_POLY_CAPACITY,
};
use crate::storage_layout::address_storage_layer;
use crate::upstream::{Field, GKRAddress};
use crate::GpuGKRStorage;

const FIRST_ACCESS_BIT: u16 = 1 << 15;

struct ResolvedStorage<'a, E> {
    backing: &'a Arc<DeviceAllocation<E>>,
    log2_stride: u32,
    poly_index: usize,
}

fn resolve_storage<B, E>(
    storage: &GpuGKRStorage<B, E>,
    address: GKRAddress,
) -> Result<ResolvedStorage<'_, E>, DrWindowBindError> {
    let poly =
        storage
            .get_ext_poly_for_address(address)
            .ok_or(DrWindowBindError::MissingSource {
                address,
                logical_layer: address_storage_layer(address),
            })?;
    assert_eq!(
        poly.offset % poly.len,
        0,
        "DR source must start at a column boundary"
    );
    Ok(ResolvedStorage {
        backing: &poly.backing,
        log2_stride: poly.len.ilog2(),
        poly_index: poly.offset / poly.len,
    })
}

fn source_column_offset(log2_stride: u32, poly_index: usize) -> Result<usize, DrWindowBindError> {
    1usize
        .checked_shl(log2_stride)
        .and_then(|stride| poly_index.checked_mul(stride))
        .ok_or(DrWindowBindError::ArenaGeometryOverflow {
            log2_stride,
            poly_count: poly_index + 1,
        })
}

pub(crate) fn source_column_pointers<E>(
    base: *const E,
    stride: usize,
    count: usize,
) -> Vec<*const E> {
    (0..count)
        .map(|index| base.wrapping_add(index * stride))
        .collect()
}

/// Retains raw canonical backings in first-use order until the last queued reader.
pub(crate) struct DrRawInputKeepalive<E> {
    backings: Vec<Arc<DeviceAllocation<E>>>,
}

impl<E> DrRawInputKeepalive<E> {
    pub(crate) fn from_projection<B>(
        storage: &GpuGKRStorage<B, E>,
        projection: &DrWindowInputProjection,
    ) -> Result<Self, DrWindowBindError> {
        let mut seen = BTreeSet::new();
        let mut backings = Vec::new();
        for &address in projection.canonical_sources() {
            let backing = Arc::clone(resolve_storage(storage, address)?.backing);
            if seen.insert(Arc::as_ptr(&backing) as usize) {
                backings.push(backing);
            }
        }
        Ok(Self { backings })
    }

    pub(crate) fn canonical_source_pointers<B>(
        &self,
        storage: &GpuGKRStorage<B, E>,
        projection: &DrWindowInputProjection,
    ) -> Result<Vec<*const E>, DrWindowBindError> {
        projection
            .canonical_sources()
            .iter()
            .copied()
            .map(|address| {
                let resolved = resolve_storage(storage, address)?;
                assert!(
                    self.backings
                        .iter()
                        .any(|backing| Arc::ptr_eq(backing, resolved.backing)),
                    "the prepared raw-input keepalive must own the resolved backing"
                );
                let offset = source_column_offset(resolved.log2_stride, resolved.poly_index)?;
                Ok(resolved.backing.as_ptr().wrapping_add(offset))
            })
            .collect()
    }
}

/// Slot assignment is in first-use order; records own first-access publication bits.
pub(crate) struct DrCompactSourceTable {
    tables: GpuGKRDimensionReducingTables,
    by_backing: BTreeMap<usize, usize>,
    slot_count: usize,
}

impl DrCompactSourceTable {
    pub(crate) fn new() -> Self {
        Self {
            tables: GpuGKRDimensionReducingTables::default(),
            by_backing: BTreeMap::new(),
            slot_count: 0,
        }
    }

    pub(crate) fn intern_storage<B, E>(
        &mut self,
        storage: &GpuGKRStorage<B, E>,
        address: GKRAddress,
    ) -> Result<u16, DrWindowBindError> {
        let resolved = resolve_storage(storage, address)?;
        self.intern(
            resolved.backing.as_ptr().cast(),
            resolved.log2_stride,
            resolved.poly_index,
        )
    }

    pub(crate) fn intern_arena(
        &mut self,
        arena: FoldingArenaBinding,
        poly_index: usize,
    ) -> Result<u16, DrWindowBindError> {
        self.intern(arena.base, arena.log2_stride, poly_index)
    }

    fn intern(
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

    pub(crate) fn finish(self) -> GpuGKRDimensionReducingTables {
        self.tables
    }
}

pub(crate) fn assemble_r0_batch<E: Field>(
    program: &DrWindowProgram,
    eq_low: *const E,
    eq_sizes: GkrEqSizes,
    mut intern_source: impl FnMut(
        &mut DrCompactSourceTable,
        GKRAddress,
    ) -> Result<u16, DrWindowBindError>,
) -> Result<GpuGKRDimensionReducingBatch<E>, DrWindowBindError> {
    assemble_records(program, eq_low, eq_sizes, |table, _, slot| {
        let mut inputs = [GpuGKRSourceRecord::default(); 2];
        for (operand, source) in slot.source_ids().iter().copied().enumerate() {
            let address = program.sources()[usize::from(source)];
            inputs[operand] = GpuGKRSourceRecord::source_only(intern_source(table, address)?);
        }
        Ok(inputs)
    })
}

pub(crate) fn assemble_continuation_batch<E: Field>(
    program: &DrWindowProgram,
    projection: &DrWindowInputProjection,
    eq_low: *const E,
    eq_sizes: GkrEqSizes,
    destination: FoldingArenaBinding,
    mut intern_source: impl FnMut(
        &mut DrCompactSourceTable,
        GKRAddress,
        u16,
    ) -> Result<u16, DrWindowBindError>,
) -> Result<GpuGKRDimensionReducingBatch<E>, DrWindowBindError> {
    let mut first_access_seen = BTreeSet::new();
    assemble_records(program, eq_low, eq_sizes, |table, dense_slot, slot| {
        let mut inputs = [GpuGKRSourceRecord::default(); 2];
        for (input_operand, record) in inputs.iter_mut().enumerate() {
            let publication_index = projection
                .publication_index(dense_slot, input_operand)
                .ok_or(DrWindowBindError::MissingPublicationIndex {
                    dense_slot,
                    input_operand,
                })?;
            let publication = usize::from(publication_index);
            if publication >= projection.canonical_sources().len() {
                return Err(DrWindowBindError::PublicationIndexOverflow {
                    publication_index: publication,
                    canonical_source_count: projection.canonical_sources().len(),
                });
            }
            let address = program.sources()[usize::from(slot.source_ids()[input_operand])];
            let source_base = intern_source(table, address, publication_index)?;
            assert_eq!(
                source_base & FIRST_ACCESS_BIT,
                0,
                "compact source tables must return a clear first-access bit"
            );
            let cache_base = table.intern_arena(destination, publication)?;
            assert_eq!(
                cache_base & FIRST_ACCESS_BIT,
                0,
                "compact destination tables must return a clear first-access bit"
            );
            let first_access = first_access_seen.insert(publication_index);
            *record = GpuGKRSourceRecord::new(
                source_base | if first_access { FIRST_ACCESS_BIT } else { 0 },
                cache_base,
            );
        }
        Ok(inputs)
    })
}

fn assemble_records<E: Field>(
    program: &DrWindowProgram,
    eq_low: *const E,
    eq_sizes: GkrEqSizes,
    mut records: impl FnMut(
        &mut DrCompactSourceTable,
        usize,
        &gpu_gkr_compiler::DrWindowSlotPlan,
    ) -> Result<[GpuGKRSourceRecord; 2], DrWindowBindError>,
) -> Result<GpuGKRDimensionReducingBatch<E>, DrWindowBindError> {
    let mut batch = GpuGKRDimensionReducingBatch {
        enabled_mask: program.enabled_mask(),
        eq_low,
        eq_sizes,
        ..Default::default()
    };
    let mut table = DrCompactSourceTable::new();
    for (dense_slot, slot) in program.slots().iter().enumerate() {
        batch.slots[slot.slot()] = GpuGKRDimensionReducingSlot {
            inputs: records(&mut table, dense_slot, slot)?,
            batch_exp: *slot.batch_exponents(),
        };
    }
    batch.tables = table.finish();
    Ok(batch)
}
