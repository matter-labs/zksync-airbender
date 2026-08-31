use core::mem::{align_of, offset_of, size_of};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use std::sync::Arc;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::E4;
use gpu_gkr_compiler::{DrWindowInputProjection, DrWindowProgram, KERNEL_ARGUMENT_CEILING_BYTES};
use gpu_prover_context::ProverContext;

use crate::backward::kernels::{
    get_eq_high_constant_device_ptr, launch_build_eq_high_and_low_groups_from_point,
    launch_build_eq_independent_groups_from_point, make_eq_sizes, pack_source_u16,
    FoldingArenaBinding, GpuGKRDimensionReducingBatch, GpuGKRDimensionReducingSlot,
    GpuGKRDimensionReducingTables, GpuGKRSourceRecord, GKR_BACKWARD_MAX_TRACE_LEN_LOG2,
    GKR_DIM_REDUCING_BASE_SLOTS, GKR_DIM_REDUCING_POLY_CAPACITY,
};
use crate::gkr_address_audit::AddressClass;
use crate::storage_layout::{address_storage_layer, FieldType};
use crate::upstream::GKRAddress;
use crate::GpuGKRStorage;

use super::composition::{
    plan_dr_window_continuations, DrWindowContinuationArenaOwners, DrWindowContinuationParity,
    DrWindowContinuationPass, DrWindowContinuationPassGeometry, DrWindowContinuationPlannedSource,
    DrWindowLayerCompositionHook, DrWindowLayerPreparationHook, DrWindowPassEqState,
    DrWindowPassEqView, DrWindowRawInputKeepalive,
};
use super::generated_registry::{
    DrWindowContinuationKernelEntry, DrWindowKernelEntry, GkrDrContinuationWindow3Arguments,
    GkrDrContinuationWindow3Signature, GkrDrR0Window3Arguments, GkrDrR0Window3Signature,
    DR_WINDOWED_CONT_BLOCK_THREADS, DR_WINDOWED_CONT_DEFINED_MASK,
    DR_WINDOWED_CONT_UNIVERSAL_KERNEL, DR_WINDOWED_R0_BLOCK_THREADS, DR_WINDOWED_R0_DEFINED_MASK,
    DR_WINDOWED_R0_UNIVERSAL_KERNEL,
};

const DR_WINDOW_COORDINATES: usize = 3;
const DR_WINDOW_ROWS_PER_TILE: usize = 32;
const DR_WINDOW_TENSOR_CELLS: usize = 27;
const DR_WINDOW_MIN_FOLDING_STEPS: usize = 4;
const DR_WINDOW_MAX_FOLDING_STEPS: usize = GKR_BACKWARD_MAX_TRACE_LEN_LOG2;
const DR_CONTINUATION_FIRST_ACCESS_BIT: u16 = 1 << 15;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrContinuationFactoredEqCapacities {
    pub(crate) high: [usize; 2],
    pub(crate) low: usize,
}

impl DrContinuationFactoredEqCapacities {
    fn table_cells(bits: u32) -> usize {
        1usize << bits
    }

    pub(crate) fn from_geometries(geometries: &[DrWindowContinuationPassGeometry]) -> Self {
        assert!(
            !geometries.is_empty(),
            "continuation Eq capacities require at least one prepared pass",
        );
        let mut max_bits = [0u32; 3];
        for geometry in geometries {
            for (destination, observed) in max_bits.iter_mut().zip([
                geometry.eq_entry_sizes.high[0],
                geometry.eq_entry_sizes.high[1],
                geometry.eq_entry_sizes.low,
            ]) {
                *destination = (*destination).max(observed);
            }
        }
        Self {
            high: [
                Self::table_cells(max_bits[0]),
                Self::table_cells(max_bits[1]),
            ],
            low: Self::table_cells(max_bits[2]),
        }
    }

    pub(crate) fn supports(self, sizes: crate::backward::GkrEqSizes) -> bool {
        self.high[0] >= Self::table_cells(sizes.high[0])
            && self.high[1] >= Self::table_cells(sizes.high[1])
            && self.low >= Self::table_cells(sizes.low)
    }
}

/// Three independently owned factored-Eq tables shared in exec-stream order
/// by one layer's continuation passes. Inactive high tables retain one E4
/// identity sentinel; active tables retain the exact maximum required by the
/// immutable prepared pass geometry.
pub(crate) struct DrContinuationFactoredEqScratch {
    high: [DeviceAllocation<E4>; 2],
    low: DeviceAllocation<E4>,
    capacities: DrContinuationFactoredEqCapacities,
}

impl DrContinuationFactoredEqScratch {
    pub(crate) fn allocate(
        context: &ProverContext,
        geometries: &[DrWindowContinuationPassGeometry],
    ) -> CudaResult<Self> {
        let capacities = DrContinuationFactoredEqCapacities::from_geometries(geometries);
        Ok(Self {
            high: [
                context.alloc(capacities.high[0], AllocationPlacement::Top)?,
                context.alloc(capacities.high[1], AllocationPlacement::Top)?,
            ],
            low: context.alloc(capacities.low, AllocationPlacement::Top)?,
            capacities,
        })
    }

    pub(crate) fn view_for_pass(
        &self,
        folding_steps: usize,
        start_round: usize,
    ) -> Result<DrContinuationFactoredEqView, DrWindowBindError> {
        let view = DrContinuationFactoredEqView::for_pass(
            self.high[0].as_ptr().cast_mut(),
            self.high[1].as_ptr().cast_mut(),
            self.low.as_ptr().cast_mut(),
            folding_steps,
            start_round,
        )?;
        assert!(
            self.capacities.supports(view.sizes),
            "prepared continuation Eq capacity must cover every pass",
        );
        Ok(view)
    }
}

/// Immutable, pass-local view into [`DrContinuationFactoredEqScratch`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DrContinuationFactoredEqView {
    pub(crate) high_0: *mut E4,
    pub(crate) high_1: *mut E4,
    pub(crate) low: *mut E4,
    pub(crate) sizes: crate::backward::GkrEqSizes,
    pub(crate) challenge_offset: u32,
    pub(crate) challenge_count: u32,
}

impl DrContinuationFactoredEqView {
    pub(crate) fn for_pass(
        high_0: *mut E4,
        high_1: *mut E4,
        low: *mut E4,
        folding_steps: usize,
        start_round: usize,
    ) -> Result<Self, DrWindowBindError> {
        if start_round < DR_WINDOW_COORDINATES
            || !start_round.is_multiple_of(DR_WINDOW_COORDINATES)
            || start_round + DR_WINDOW_COORDINATES >= folding_steps
        {
            return Err(DrWindowBindError::InvalidContinuationBoundary {
                folding_steps,
                start_round,
            });
        }
        let challenge_offset = start_round + DR_WINDOW_COORDINATES;
        let challenge_count = folding_steps - challenge_offset;
        Ok(Self::new(
            high_0,
            high_1,
            low,
            make_eq_sizes(challenge_count),
            challenge_offset as u32,
            challenge_count as u32,
        ))
    }

    pub(crate) const fn new(
        high_0: *mut E4,
        high_1: *mut E4,
        low: *mut E4,
        sizes: crate::backward::GkrEqSizes,
        challenge_offset: u32,
        challenge_count: u32,
    ) -> Self {
        Self {
            high_0,
            high_1,
            low,
            sizes,
            challenge_offset,
            challenge_count,
        }
    }
}

// SAFETY: views contain device pointers only and are forwarded exclusively to
// stream-ordered kernels while the owning scratch remains alive.
unsafe impl Send for DrContinuationFactoredEqView {}
unsafe impl Sync for DrContinuationFactoredEqView {}

/// Resolve the next global Eq group without consulting R0's constant slab.
pub(crate) fn resolve_dr_global_active_eq_slot(
    view: &DrContinuationFactoredEqView,
) -> (*mut E4, u32) {
    if view.sizes.low > 0 {
        (view.low, view.sizes.low)
    } else if view.sizes.high[1] > 0 {
        (view.high_1, view.sizes.high[1])
    } else {
        debug_assert!(view.sizes.high[0] >= 1);
        (view.high_0, view.sizes.high[0])
    }
}

/// One arena allocation plus the immutable metadata needed to derive compact
/// source bindings. Cloning the `Arc` retains the same allocation; it never
/// allocates a second backing.
pub(crate) struct DrWindowContinuationArena {
    allocation: Rc<DeviceAllocation<E4>>,
    log2_stride: u32,
    poly_count: usize,
}

impl DrWindowContinuationArena {
    pub(crate) fn allocate(
        context: &ProverContext,
        log2_stride: u32,
        poly_count: usize,
    ) -> Result<Self, DrWindowBindError> {
        let per_poly_len =
            1usize
                .checked_shl(log2_stride)
                .ok_or(DrWindowBindError::ArenaGeometryOverflow {
                    log2_stride,
                    poly_count,
                })?;
        let required = per_poly_len.checked_mul(poly_count).ok_or(
            DrWindowBindError::ArenaGeometryOverflow {
                log2_stride,
                poly_count,
            },
        )?;
        let allocation = Rc::new(context.alloc(required, AllocationPlacement::Top)?);
        Self::new(allocation, log2_stride, poly_count)
    }

    pub(crate) fn new(
        allocation: Rc<DeviceAllocation<E4>>,
        log2_stride: u32,
        poly_count: usize,
    ) -> Result<Self, DrWindowBindError> {
        let per_poly_len =
            1usize
                .checked_shl(log2_stride)
                .ok_or(DrWindowBindError::ArenaGeometryOverflow {
                    log2_stride,
                    poly_count,
                })?;
        let required = per_poly_len.checked_mul(poly_count).ok_or(
            DrWindowBindError::ArenaGeometryOverflow {
                log2_stride,
                poly_count,
            },
        )?;
        if allocation.len() < required {
            return Err(DrWindowBindError::ArenaCapacity {
                required,
                capacity: allocation.len(),
            });
        }
        Ok(Self {
            allocation,
            log2_stride,
            poly_count,
        })
    }

    pub(crate) fn binding(&self) -> FoldingArenaBinding {
        FoldingArenaBinding::new(self.allocation.as_ptr().cast(), self.log2_stride)
    }

    /// Reuse the same allocation with the smaller per-poly prefix of a later
    /// same-parity pass. This clones ownership metadata only; it performs no
    /// device allocation.
    pub(crate) fn with_geometry(
        &self,
        log2_stride: u32,
        poly_count: usize,
    ) -> Result<Self, DrWindowBindError> {
        Self::new(Rc::clone(&self.allocation), log2_stride, poly_count)
    }

    pub(crate) fn poly_count(&self) -> usize {
        self.poly_count
    }
}

pub(crate) enum DrWindowContinuationSource<'a, B> {
    Storage(&'a GpuGKRStorage<B, E4>),
    Arena(&'a DrWindowContinuationArena),
}

/// The by-value ABI passed to the universal DR R0 producer.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub(crate) struct DrWindowLaunchBinding {
    pub(crate) batch: GpuGKRDimensionReducingBatch<E4>,
    pub(crate) partials: *mut E4,
    pub(crate) log_rows: u32,
    pub(crate) reserved: u32,
}

/// The by-value ABI passed to the universal DR continuation producer.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub(crate) struct DrWindowContinuationLaunchBinding {
    pub(crate) batch: GpuGKRDimensionReducingBatch<E4>,
    pub(crate) eq_high_0: *const E4,
    pub(crate) eq_high_1: *const E4,
    pub(crate) partials: *mut E4,
    pub(crate) claim_point: *const E4,
    pub(crate) log_rows: u32,
    pub(crate) start_round: u32,
    pub(crate) reserved: [u32; 2],
}

const _: () = {
    assert!(size_of::<GpuGKRDimensionReducingBatch<E4>>() == 336);
    assert!(size_of::<DrWindowLaunchBinding>() == 352);
    assert!(align_of::<DrWindowLaunchBinding>() == 16);
    assert!(size_of::<DrWindowLaunchBinding>() <= KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(offset_of!(DrWindowLaunchBinding, batch) == 0);
    assert!(offset_of!(DrWindowLaunchBinding, partials) == 336);
    assert!(offset_of!(DrWindowLaunchBinding, log_rows) == 344);
    assert!(offset_of!(DrWindowLaunchBinding, reserved) == 348);
};

const _: () = {
    assert!(size_of::<DrWindowContinuationLaunchBinding>() == 384);
    assert!(align_of::<DrWindowContinuationLaunchBinding>() == 16);
    assert!(size_of::<DrWindowContinuationLaunchBinding>() <= KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(offset_of!(DrWindowContinuationLaunchBinding, batch) == 0);
    assert!(offset_of!(DrWindowContinuationLaunchBinding, eq_high_0) == 336);
    assert!(offset_of!(DrWindowContinuationLaunchBinding, eq_high_1) == 344);
    assert!(offset_of!(DrWindowContinuationLaunchBinding, partials) == 352);
    assert!(offset_of!(DrWindowContinuationLaunchBinding, claim_point) == 360);
    assert!(offset_of!(DrWindowContinuationLaunchBinding, log_rows) == 368);
    assert!(offset_of!(DrWindowContinuationLaunchBinding, start_round) == 372);
    assert!(offset_of!(DrWindowContinuationLaunchBinding, reserved) == 376);
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum DrWindowBindError {
    Cuda(era_cudart_sys::CudaError),
    ZeroMask,
    UndefinedMaskBits {
        bits: u32,
    },
    UnsupportedFoldingSteps {
        folding_steps: usize,
    },
    ScratchCapacity {
        required: usize,
        capacity: usize,
    },
    EqBuildOffset {
        expected: usize,
        observed: usize,
    },
    EqSizeMismatch,
    InvalidContinuationBoundary {
        folding_steps: usize,
        start_round: usize,
    },
    ContinuationPlanMismatch {
        window_count: usize,
        entry_round: usize,
    },
    ContinuationsAlreadyBound,
    MissingPublicationIndex {
        dense_slot: usize,
        input_operand: usize,
    },
    PublicationIndexOverflow {
        publication_index: usize,
        canonical_source_count: usize,
    },
    ArenaGeometryOverflow {
        log2_stride: u32,
        poly_count: usize,
    },
    ArenaCapacity {
        required: usize,
        capacity: usize,
    },
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
    FinalPublicationStrideMismatch {
        owner_log2_stride: u32,
        planned_log2_stride: u32,
        planned_per_poly_len: usize,
    },
    BaseSlotOverflow {
        required: usize,
        capacity: usize,
    },
    PolyIndexOverflow {
        poly_index: usize,
        capacity: usize,
    },
    NullContinuationPointer {
        pointer: &'static str,
    },
    NullContinuationTableBase {
        slot: usize,
        input_operand: usize,
        table_slot: usize,
        destination: bool,
    },
    ContinuationEqAliasedPointers {
        first: &'static str,
        second: &'static str,
    },
    ContinuationEqLowMismatch,
    ContinuationContributionsMustBeNull,
}

impl From<era_cudart_sys::CudaError> for DrWindowBindError {
    fn from(error: era_cudart_sys::CudaError) -> Self {
        Self::Cuda(error)
    }
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
    /// Continuation assembly sets the first-access bit after deduplication.
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

/// Runtime allocation bound by the producer. The first `27 * row_tiles` cells
/// are row-tile-major partials; the final 27 cells are reserved for the split
/// tensor tail.
#[derive(Clone, Copy, Debug)]
pub(crate) struct DrWindowRuntimeScratch {
    pub(crate) partials: *mut E4,
    pub(crate) partials_capacity: usize,
}

pub(crate) fn dr_window_row_tiles(folding_steps: usize) -> usize {
    let log_rows = folding_steps - DR_WINDOW_COORDINATES;
    (1usize << log_rows)
        .div_ceil(DR_WINDOW_ROWS_PER_TILE)
        .max(1)
}

pub(crate) fn dr_window_log_rows(folding_steps: usize) -> u32 {
    assert!(folding_steps >= DR_WINDOW_COORDINATES);
    (folding_steps - DR_WINDOW_COORDINATES) as u32
}

pub(crate) fn dr_window_partials_len(folding_steps: usize) -> usize {
    DR_WINDOW_TENSOR_CELLS * (dr_window_row_tiles(folding_steps) + 1)
}

pub(crate) fn dr_window_reduced_tensor(partials: *mut E4, row_tiles: usize) -> *mut E4 {
    assert!(!partials.is_null());
    assert!(row_tiles > 0);
    // SAFETY: every binding path first checks capacity for the row-tile matrix
    // plus this 27-cell reduced-tensor suffix.
    unsafe { partials.add(DR_WINDOW_TENSOR_CELLS * row_tiles) }
}

pub(super) fn validate_dr_window_folding_steps(
    folding_steps: usize,
) -> Result<(), DrWindowBindError> {
    if !(DR_WINDOW_MIN_FOLDING_STEPS..=DR_WINDOW_MAX_FOLDING_STEPS).contains(&folding_steps) {
        return Err(DrWindowBindError::UnsupportedFoldingSteps { folding_steps });
    }
    Ok(())
}

pub(super) fn validate_dr_r0_eq_contract(
    folding_steps: usize,
    build_offset: usize,
    eq_sizes: crate::backward::GkrEqSizes,
) -> Result<(), DrWindowBindError> {
    if build_offset != DR_WINDOW_COORDINATES {
        return Err(DrWindowBindError::EqBuildOffset {
            expected: DR_WINDOW_COORDINATES,
            observed: build_offset,
        });
    }
    if eq_sizes != make_eq_sizes(folding_steps - DR_WINDOW_COORDINATES) {
        return Err(DrWindowBindError::EqSizeMismatch);
    }
    Ok(())
}

/// A launch-ready universal DR R0 tensor producer.
pub(crate) struct DrWindowLaunch {
    pub(crate) binding: Box<DrWindowLaunchBinding>,
    pub(crate) kernel: &'static DrWindowKernelEntry,
    pub(crate) row_tiles: usize,
    pub(crate) reduced_tensor: *mut E4,
    pub(crate) folding_steps: usize,
}

/// One launch-ready input-only DR continuation tensor producer.
pub(crate) struct DrWindowContinuationLaunch {
    pub(crate) binding: Box<DrWindowContinuationLaunchBinding>,
    pub(crate) kernel: &'static DrWindowContinuationKernelEntry,
    pub(crate) row_tiles: usize,
    pub(crate) reduced_tensor: *mut E4,
    pub(crate) folding_steps: usize,
    pub(crate) start_round: usize,
}

// SAFETY: the raw pointers are only forwarded to stream-ordered kernels.
unsafe impl Send for DrWindowLaunch {}
unsafe impl Sync for DrWindowLaunch {}

// SAFETY: the raw pointers are only forwarded to stream-ordered kernels.
unsafe impl Send for DrWindowContinuationLaunch {}
unsafe impl Sync for DrWindowContinuationLaunch {}

pub(crate) fn resolve_dr_window_kernel(
    mask: u32,
) -> Result<&'static DrWindowKernelEntry, DrWindowBindError> {
    let undefined = mask & !DR_WINDOWED_R0_DEFINED_MASK;
    if undefined != 0 {
        return Err(DrWindowBindError::UndefinedMaskBits { bits: undefined });
    }
    if mask == 0 {
        return Err(DrWindowBindError::ZeroMask);
    }
    Ok(&DR_WINDOWED_R0_UNIVERSAL_KERNEL)
}

pub(crate) fn resolve_dr_window_continuation_kernel(
    mask: u32,
) -> Result<&'static DrWindowContinuationKernelEntry, DrWindowBindError> {
    let undefined = mask & !DR_WINDOWED_CONT_DEFINED_MASK;
    if undefined != 0 {
        return Err(DrWindowBindError::UndefinedMaskBits { bits: undefined });
    }
    if mask == 0 {
        return Err(DrWindowBindError::ZeroMask);
    }
    Ok(&DR_WINDOWED_CONT_UNIVERSAL_KERNEL)
}

/// Assemble the input-only continuation batch. This is the single owner of
/// per-launch first-access state: source interning supplies an already packed,
/// bit-15-clear base, and this function only adds the publication bit.
pub(super) fn assemble_dr_window_continuation_batch(
    program: &DrWindowProgram,
    projection: &DrWindowInputProjection,
    eq: DrContinuationFactoredEqView,
    destination: FoldingArenaBinding,
    mut intern_source: impl FnMut(
        &mut DrCompactSourceTableBuilder,
        GKRAddress,
        u16,
    ) -> Result<u16, DrWindowBindError>,
) -> Result<GpuGKRDimensionReducingBatch<E4>, DrWindowBindError> {
    let mut batch = GpuGKRDimensionReducingBatch::<E4> {
        enabled_mask: program.enabled_mask(),
        eq_low: eq.low.cast_const(),
        eq_sizes: eq.sizes,
        ..Default::default()
    };
    let mut table_builder = DrCompactSourceTableBuilder::new();
    let mut first_access_seen = BTreeSet::<u16>::new();
    for (dense_slot, slot) in program.slots().iter().enumerate() {
        let mut io = [GpuGKRSourceRecord::default(); 4];
        for (input_operand, record) in io.iter_mut().enumerate().take(2) {
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
            let source_id = slot.source_ids()[input_operand];
            let address = program.sources()[usize::from(source_id)];
            let source_base = intern_source(&mut table_builder, address, publication_index)?;
            assert_eq!(
                source_base & DR_CONTINUATION_FIRST_ACCESS_BIT,
                0,
                "compact source-table builders must return a clear first-access bit",
            );
            let cache_base = table_builder.intern_arena_e4(destination, publication)?;
            assert_eq!(
                cache_base & DR_CONTINUATION_FIRST_ACCESS_BIT,
                0,
                "compact destination-table builders must return a clear first-access bit",
            );
            let first_access = first_access_seen.insert(publication_index);
            let source = source_base
                | if first_access {
                    DR_CONTINUATION_FIRST_ACCESS_BIT
                } else {
                    0
                };
            *record = GpuGKRSourceRecord::new(source, cache_base);
        }
        batch.slots[slot.slot()] = GpuGKRDimensionReducingSlot {
            io,
            batch_exp: *slot.batch_exponents(),
        };
    }
    batch.tables = table_builder.finish();
    debug_assert!(batch.contributions.is_null());
    Ok(batch)
}

pub(crate) fn build_dr_window_continuation_batch<B>(
    program: &DrWindowProgram,
    projection: &DrWindowInputProjection,
    source: &DrWindowContinuationSource<'_, B>,
    destination: &DrWindowContinuationArena,
    eq: DrContinuationFactoredEqView,
) -> Result<GpuGKRDimensionReducingBatch<E4>, DrWindowBindError> {
    if destination.poly_count() < projection.canonical_sources().len() {
        return Err(DrWindowBindError::ArenaCapacity {
            required: projection.canonical_sources().len(),
            capacity: destination.poly_count(),
        });
    }
    match source {
        DrWindowContinuationSource::Storage(storage) => assemble_dr_window_continuation_batch(
            program,
            projection,
            eq,
            destination.binding(),
            |builder, address, _| builder.intern_storage_e4(storage, address),
        ),
        DrWindowContinuationSource::Arena(arena) => {
            if arena.poly_count() < projection.canonical_sources().len() {
                return Err(DrWindowBindError::ArenaCapacity {
                    required: projection.canonical_sources().len(),
                    capacity: arena.poly_count(),
                });
            }
            assemble_dr_window_continuation_batch(
                program,
                projection,
                eq,
                destination.binding(),
                |builder, _, publication_index| {
                    builder.intern_arena_e4(arena.binding(), usize::from(publication_index))
                },
            )
        }
    }
}

pub(super) fn validate_dr_window_continuation_eq_contract(
    folding_steps: usize,
    start_round: usize,
    eq: DrContinuationFactoredEqView,
) -> Result<(), DrWindowBindError> {
    if start_round < DR_WINDOW_COORDINATES
        || !start_round.is_multiple_of(DR_WINDOW_COORDINATES)
        || start_round + DR_WINDOW_COORDINATES >= folding_steps
    {
        return Err(DrWindowBindError::InvalidContinuationBoundary {
            folding_steps,
            start_round,
        });
    }
    let expected_offset = start_round + DR_WINDOW_COORDINATES;
    if eq.challenge_offset as usize != expected_offset {
        return Err(DrWindowBindError::EqBuildOffset {
            expected: expected_offset,
            observed: eq.challenge_offset as usize,
        });
    }
    let expected_count = folding_steps - expected_offset;
    if eq.challenge_count as usize != expected_count || eq.sizes != make_eq_sizes(expected_count) {
        return Err(DrWindowBindError::EqSizeMismatch);
    }
    if eq.high_0.is_null() {
        return Err(DrWindowBindError::NullContinuationPointer {
            pointer: "eq_high_0",
        });
    }
    if eq.high_1.is_null() {
        return Err(DrWindowBindError::NullContinuationPointer {
            pointer: "eq_high_1",
        });
    }
    if eq.low.is_null() {
        return Err(DrWindowBindError::NullContinuationPointer { pointer: "eq_low" });
    }
    for (first_name, first, second_name, second) in [
        ("eq_high_0", eq.high_0, "eq_high_1", eq.high_1),
        ("eq_high_0", eq.high_0, "eq_low", eq.low),
        ("eq_high_1", eq.high_1, "eq_low", eq.low),
    ] {
        if first == second {
            return Err(DrWindowBindError::ContinuationEqAliasedPointers {
                first: first_name,
                second: second_name,
            });
        }
    }
    Ok(())
}

fn validate_dr_window_continuation_table_bases(
    batch: &GpuGKRDimensionReducingBatch<E4>,
) -> Result<(), DrWindowBindError> {
    for (slot, descriptor) in batch.slots.iter().enumerate() {
        if batch.enabled_mask & (1 << slot) == 0 {
            continue;
        }
        for input_operand in 0..2 {
            let record = descriptor.io[input_operand];
            let source_slot = usize::from((record.src >> 11) & 0x0f);
            if batch.tables.bases[source_slot].is_null() {
                return Err(DrWindowBindError::NullContinuationTableBase {
                    slot,
                    input_operand,
                    table_slot: source_slot,
                    destination: false,
                });
            }
            let destination_slot = usize::from((record.cache >> 11) & 0x0f);
            if batch.tables.bases[destination_slot].is_null() {
                return Err(DrWindowBindError::NullContinuationTableBase {
                    slot,
                    input_operand,
                    table_slot: destination_slot,
                    destination: true,
                });
            }
        }
    }
    Ok(())
}

/// Bind one input-only continuation launch. D3 owns source/arena composition;
/// this D2 seam validates an already assembled batch without allocating.
pub(super) fn bind_dr_window_continuation_launch(
    batch: GpuGKRDimensionReducingBatch<E4>,
    folding_steps: usize,
    start_round: usize,
    eq: DrContinuationFactoredEqView,
    scratch: DrWindowRuntimeScratch,
    claim_point: *const E4,
) -> Result<DrWindowContinuationLaunch, DrWindowBindError> {
    validate_dr_window_folding_steps(folding_steps)?;
    validate_dr_window_continuation_eq_contract(folding_steps, start_round, eq)?;
    let kernel = resolve_dr_window_continuation_kernel(batch.enabled_mask)?;
    if scratch.partials.is_null() {
        return Err(DrWindowBindError::NullContinuationPointer {
            pointer: "partials",
        });
    }
    if claim_point.is_null() {
        return Err(DrWindowBindError::NullContinuationPointer {
            pointer: "claim_point",
        });
    }
    if batch.eq_low != eq.low.cast_const() {
        return Err(DrWindowBindError::ContinuationEqLowMismatch);
    }
    if batch.eq_sizes != eq.sizes {
        return Err(DrWindowBindError::EqSizeMismatch);
    }
    if !batch.contributions.is_null() {
        return Err(DrWindowBindError::ContinuationContributionsMustBeNull);
    }
    validate_dr_window_continuation_table_bases(&batch)?;

    let suffix_log = folding_steps - start_round;
    let required = dr_window_partials_len(suffix_log);
    if scratch.partials_capacity < required {
        return Err(DrWindowBindError::ScratchCapacity {
            required,
            capacity: scratch.partials_capacity,
        });
    }
    let row_tiles = dr_window_row_tiles(suffix_log);
    let reduced_tensor = dr_window_reduced_tensor(scratch.partials, row_tiles);
    Ok(DrWindowContinuationLaunch {
        binding: Box::new(DrWindowContinuationLaunchBinding {
            batch,
            eq_high_0: eq.high_0.cast_const(),
            eq_high_1: eq.high_1.cast_const(),
            partials: scratch.partials,
            claim_point,
            log_rows: dr_window_log_rows(suffix_log),
            start_round: start_round as u32,
            reserved: [0; 2],
        }),
        kernel,
        row_tiles,
        reduced_tensor,
        folding_steps,
        start_round,
    })
}

fn build_dr_window_batch<B>(
    program: &DrWindowProgram,
    storage: &GpuGKRStorage<B, E4>,
    eq: DrWindowPassEqView,
) -> Result<GpuGKRDimensionReducingBatch<E4>, DrWindowBindError> {
    let mut batch = GpuGKRDimensionReducingBatch::<E4> {
        enabled_mask: program.enabled_mask(),
        eq_low: eq.eq_low,
        eq_sizes: eq.eq_sizes,
        ..Default::default()
    };
    let mut table_builder = DrCompactSourceTableBuilder::new();
    for slot in program.slots() {
        let mut io = [GpuGKRSourceRecord::default(); 4];
        for (operand, source_id) in slot.source_ids().iter().copied().enumerate() {
            let address = program.sources()[usize::from(source_id)];
            io[operand] =
                GpuGKRSourceRecord::source_only(table_builder.intern_storage_e4(storage, address)?);
        }
        batch.slots[slot.slot()] = GpuGKRDimensionReducingSlot {
            io,
            batch_exp: *slot.batch_exponents(),
        };
    }
    batch.tables = table_builder.finish();
    debug_assert!(batch.contributions.is_null());
    Ok(batch)
}

/// Allocate and bind the exact continuation prefix already selected by the
/// landed R0 hook. All descriptor pointers are retained by `hook`: raw input
/// backings, the two parity arena allocations, and the single global Eq
/// scratch outlive every launch queued from the returned records.
pub(crate) fn bind_dr_window_continuations<B>(
    hook: &mut DrWindowLayerCompositionHook,
    storage: &GpuGKRStorage<B, E4>,
    claim_point: *const E4,
    context: &ProverContext,
) -> Result<(), DrWindowBindError> {
    if !hook.continuation_launches.is_empty()
        || hook.continuation_eq.is_some()
        || hook.continuation_arenas.even.is_some()
        || hook.continuation_arenas.odd.is_some()
    {
        return Err(DrWindowBindError::ContinuationsAlreadyBound);
    }

    let folding_steps = hook.r0_launch.folding_steps;
    let geometries = plan_dr_window_continuations(
        folding_steps,
        hook.continuation_window_count,
        hook.megakernel_entry_round,
    )?;
    if geometries.is_empty() {
        return Ok(());
    }

    let scratch = DrWindowRuntimeScratch {
        partials: hook.r0_launch.binding.partials,
        partials_capacity: hook.partials_capacity,
    };
    for geometry in &geometries {
        if scratch.partials_capacity < geometry.partials_len {
            return Err(DrWindowBindError::ScratchCapacity {
                required: geometry.partials_len,
                capacity: scratch.partials_capacity,
            });
        }
    }

    let poly_count = hook.continuation_projection.canonical_sources().len();
    let mut arenas = DrWindowContinuationArenaOwners::default();
    let even_geometry = geometries
        .iter()
        .find(|geometry| geometry.destination == DrWindowContinuationParity::Even)
        .expect("a nonempty continuation prefix always starts with even parity");
    arenas.even = Some(DrWindowContinuationArena::allocate(
        context,
        even_geometry.log2_stride,
        poly_count,
    )?);
    if let Some(odd_geometry) = geometries
        .iter()
        .find(|geometry| geometry.destination == DrWindowContinuationParity::Odd)
    {
        arenas.odd = Some(DrWindowContinuationArena::allocate(
            context,
            odd_geometry.log2_stride,
            poly_count,
        )?);
    }
    let eq_scratch = DrContinuationFactoredEqScratch::allocate(context, &geometries)?;
    let mut launches = Vec::with_capacity(geometries.len());

    for geometry in geometries {
        let eq_entry = eq_scratch.view_for_pass(folding_steps, geometry.start_round)?;
        debug_assert_eq!(eq_entry.sizes, geometry.eq_entry_sizes);
        debug_assert_eq!(
            eq_entry.challenge_offset as usize,
            geometry.challenge_offset
        );
        debug_assert_eq!(eq_entry.challenge_count as usize, geometry.challenge_count);

        let destination = arenas
            .get(geometry.destination)
            .expect("the first use allocated this destination parity")
            .with_geometry(geometry.log2_stride, poly_count)?;
        let source_arena = match geometry.source {
            DrWindowContinuationPlannedSource::Raw => None,
            DrWindowContinuationPlannedSource::Arena(parity) => {
                let previous_geometry = launches
                    .last()
                    .map(|pass: &DrWindowContinuationPass| pass.geometry)
                    .expect("an arena source always follows a prior pass");
                debug_assert_eq!(previous_geometry.destination, parity);
                Some(
                    arenas
                        .get(parity)
                        .expect("the prior pass allocated this source parity")
                        .with_geometry(previous_geometry.log2_stride, poly_count)?,
                )
            }
        };
        let source = source_arena
            .as_ref()
            .map_or(DrWindowContinuationSource::Storage(storage), |arena| {
                DrWindowContinuationSource::Arena(arena)
            });
        let batch = build_dr_window_continuation_batch(
            &hook.continuation_program,
            &hook.continuation_projection,
            &source,
            &destination,
            eq_entry,
        )?;
        let launch = bind_dr_window_continuation_launch(
            batch,
            folding_steps,
            geometry.start_round,
            eq_entry,
            scratch,
            claim_point,
        )?;
        launches.push(DrWindowContinuationPass {
            geometry,
            launch,
            eq_entry,
        });
    }

    debug_assert_eq!(
        launches.last().unwrap().geometry.start_round + DR_WINDOW_COORDINATES,
        hook.megakernel_entry_round,
    );
    hook.continuation_launches = launches;
    hook.continuation_eq = Some(eq_scratch);
    hook.continuation_arenas = arenas;
    Ok(())
}

pub(crate) fn prepare_dr_window_r0<B>(
    program: &DrWindowProgram,
    projection: &DrWindowInputProjection,
    storage: &GpuGKRStorage<B, E4>,
    folding_steps: usize,
    continuation_window_count: usize,
    megakernel_entry_round: usize,
    eq: DrWindowPassEqState,
    required_future_partials_len: usize,
    partials: *mut E4,
) -> Result<DrWindowLayerPreparationHook, DrWindowBindError> {
    validate_dr_window_folding_steps(folding_steps)?;
    let kernel = resolve_dr_window_kernel(program.enabled_mask())?;
    validate_dr_r0_eq_contract(folding_steps, eq.build_offset, eq.eq_sizes)?;
    let expected_partials_len = dr_window_partials_len(folding_steps);
    assert_eq!(
        required_future_partials_len, expected_partials_len,
        "the prepared chain must retain its exact partials requirement",
    );
    let raw_inputs = DrWindowRawInputKeepalive::from_projection(storage, projection)?;
    let row_tiles = dr_window_row_tiles(folding_steps);
    let batch = build_dr_window_batch(program, storage, eq.as_view())?;
    assert_eq!(
        batch.eq_low,
        eq.eq_low.as_ptr(),
        "the prepared descriptor must point at its owned common Eq allocation",
    );
    let launch = DrWindowLaunch {
        binding: Box::new(DrWindowLaunchBinding {
            batch,
            partials,
            log_rows: dr_window_log_rows(folding_steps),
            reserved: 0,
        }),
        kernel,
        row_tiles,
        reduced_tensor: dr_window_reduced_tensor(partials, row_tiles),
        folding_steps,
    };
    Ok(DrWindowLayerPreparationHook::new(
        launch,
        continuation_window_count,
        megakernel_entry_round,
        eq,
        raw_inputs,
        required_future_partials_len,
        program.clone(),
        projection.clone(),
    ))
}

impl KernelFunction for DrWindowKernelEntry {
    type Signature = GkrDrR0Window3Signature;

    fn as_ptr(&self) -> *const std::os::raw::c_void {
        self.symbol as *const std::os::raw::c_void
    }
}

impl KernelFunction for DrWindowContinuationKernelEntry {
    type Signature = GkrDrContinuationWindow3Signature;

    fn as_ptr(&self) -> *const std::os::raw::c_void {
        self.symbol as *const std::os::raw::c_void
    }
}

/// Build the one R0 pass-local factored-Eq state and then launch the producer.
/// The builder reads the device-resident claim point from offset 3; this host
/// function never dereferences it.
pub(crate) fn launch_dr_window_r0(
    hook: &DrWindowLayerCompositionHook,
    claim_point: *const E4,
    context: &ProverContext,
) -> CudaResult<()> {
    let launch = &hook.r0_launch;
    debug_assert_eq!(hook.r0_eq.build_offset, DR_WINDOW_COORDINATES);
    debug_assert_eq!(
        launch.binding.batch.eq_low,
        hook.r0_eq.eq_low.as_ptr(),
        "the descriptor must borrow the Eq allocation owned by its composition hook",
    );
    let challenge_count = launch.folding_steps - DR_WINDOW_COORDINATES;
    launch_build_eq_high_and_low_groups_from_point(
        claim_point,
        DR_WINDOW_COORDINATES,
        challenge_count,
        get_eq_high_constant_device_ptr(),
        launch.binding.batch.eq_low.cast_mut(),
        context,
    )?;
    let config = CudaLaunchConfig::basic(
        launch.row_tiles as u32,
        DR_WINDOWED_R0_BLOCK_THREADS,
        context.get_exec_stream(),
    );
    launch
        .kernel
        .launch(&config, &GkrDrR0Window3Arguments::new(*launch.binding))
}

/// Build fresh `Eq(tau[start_round + 3..folding_steps])` in the DR-owned
/// global scratch, then enqueue the universal continuation on `exec_stream`.
pub(crate) fn launch_dr_window_continuation(
    launch: &DrWindowContinuationLaunch,
    context: &ProverContext,
) -> CudaResult<()> {
    let challenge_offset = launch.start_round + DR_WINDOW_COORDINATES;
    let challenge_count = launch.folding_steps - challenge_offset;
    debug_assert_eq!(launch.binding.start_round as usize, launch.start_round);
    debug_assert_eq!(
        launch.binding.batch.eq_sizes,
        make_eq_sizes(challenge_count)
    );
    launch_build_eq_independent_groups_from_point(
        launch.binding.claim_point,
        challenge_offset,
        challenge_count,
        launch.binding.eq_high_0.cast_mut(),
        launch.binding.eq_high_1.cast_mut(),
        launch.binding.batch.eq_low.cast_mut(),
        context,
    )?;
    let config = CudaLaunchConfig::basic(
        launch.row_tiles as u32,
        DR_WINDOWED_CONT_BLOCK_THREADS,
        context.get_exec_stream(),
    );
    launch.kernel.launch(
        &config,
        &GkrDrContinuationWindow3Arguments::new(*launch.binding),
    )
}
