// Task 5 consumes the direct producer seam; Task 6 consumes layer preparation.
#![allow(dead_code)]

use core::mem::{align_of, offset_of, size_of};
use std::collections::BTreeMap;
use std::sync::Arc;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::E4;
use gpu_gkr_compiler::{DrWindowInputProjection, DrWindowProgram, KERNEL_ARGUMENT_CEILING_BYTES};
use gpu_prover_context::ProverContext;

use crate::backward::kernels::{
    get_eq_high_constant_device_ptr, launch_build_eq_high_and_low_groups_from_point, make_eq_sizes,
    pack_source_u16, FoldingArenaBinding, GpuGKRDimensionReducingBatch,
    GpuGKRDimensionReducingSlot, GpuGKRDimensionReducingTables, GpuGKRSourceRecord,
    GKR_BACKWARD_MAX_TRACE_LEN_LOG2, GKR_DIM_REDUCING_BASE_SLOTS, GKR_DIM_REDUCING_POLY_CAPACITY,
};
use crate::gkr_address_audit::AddressClass;
use crate::storage_layout::{address_storage_layer, FieldType};
use crate::upstream::GKRAddress;
use crate::GpuGKRStorage;

use super::composition::{
    DrWindowLayerCompositionHook, DrWindowLayerPreparationHook, DrWindowPassEqState,
    DrWindowPassEqView, DrWindowRawInputKeepalive,
};
use super::generated_registry::{
    DrWindowKernelEntry, GkrDrR0Window3Arguments, GkrDrR0Window3Signature,
    DR_WINDOWED_R0_BLOCK_THREADS, DR_WINDOWED_R0_DEFINED_MASK, DR_WINDOWED_R0_UNIVERSAL_KERNEL,
};

const DR_WINDOW_COORDINATES: usize = 3;
const DR_WINDOW_ROWS_PER_TILE: usize = 32;
const DR_WINDOW_TENSOR_CELLS: usize = 27;
const DR_WINDOW_MIN_FOLDING_STEPS: usize = 4;
const DR_WINDOW_MAX_FOLDING_STEPS: usize = GKR_BACKWARD_MAX_TRACE_LEN_LOG2;

/// The by-value ABI passed to the universal DR R0 producer.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub(crate) struct DrWindowLaunchBinding {
    pub(crate) batch: GpuGKRDimensionReducingBatch<E4>,
    pub(crate) partials: *mut E4,
    pub(crate) log_rows: u32,
    pub(crate) reserved: u32,
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum DrWindowBindError {
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

pub(crate) fn dr_window_partials_len(folding_steps: usize) -> usize {
    DR_WINDOW_TENSOR_CELLS * (dr_window_row_tiles(folding_steps) + 1)
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

/// Static R0 preparation retained by Task 6. Unlike `DrWindowLaunch`, this has
/// no runtime partials or reduced-tensor pointer and therefore admits no scratch
/// capacity for the future complete-chain launch.
pub(crate) struct DrWindowR0Preparation {
    pub(crate) batch: GpuGKRDimensionReducingBatch<E4>,
    pub(crate) kernel: &'static DrWindowKernelEntry,
    pub(crate) row_tiles: usize,
    pub(crate) folding_steps: usize,
    pub(crate) required_future_partials_len: usize,
}

impl DrWindowLaunch {
    pub(crate) fn selected_symbol(&self) -> &'static str {
        self.kernel.symbol_name
    }
}

// SAFETY: the raw pointers are only forwarded to stream-ordered kernels.
unsafe impl Send for DrWindowLaunch {}
unsafe impl Sync for DrWindowLaunch {}

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

/// Bind one lowered DR program without reading claim-point device memory on the
/// host. R0 owns one pass-local Eq table built at offset 3 over `f - 3` suffix
/// coordinates.
fn bind_dr_window_launch<B>(
    program: &DrWindowProgram,
    storage: &GpuGKRStorage<B, E4>,
    folding_steps: usize,
    eq: &DrWindowPassEqState,
    scratch: DrWindowRuntimeScratch,
) -> Result<DrWindowLaunch, DrWindowBindError> {
    validate_dr_window_folding_steps(folding_steps)?;
    let kernel = resolve_dr_window_kernel(program.enabled_mask())?;
    validate_dr_r0_eq_contract(folding_steps, eq.build_offset, eq.eq_sizes)?;
    let required = dr_window_partials_len(folding_steps);
    if scratch.partials_capacity < required {
        return Err(DrWindowBindError::ScratchCapacity {
            required,
            capacity: scratch.partials_capacity,
        });
    }

    let row_tiles = dr_window_row_tiles(folding_steps);
    let batch = build_dr_window_batch(program, storage, eq.as_view())?;
    // SAFETY: the capacity check reserves the complete partial matrix before
    // the 27-cell reduced-tensor suffix.
    let reduced_tensor = unsafe { scratch.partials.add(DR_WINDOW_TENSOR_CELLS * row_tiles) };
    Ok(DrWindowLaunch {
        binding: Box::new(DrWindowLaunchBinding {
            batch,
            partials: scratch.partials,
            log_rows: (folding_steps - DR_WINDOW_COORDINATES) as u32,
            reserved: 0,
        }),
        kernel,
        row_tiles,
        reduced_tensor,
        folding_steps,
    })
}

/// Bind and retain the complete R0 launch seam before legacy storage purge.
/// The returned hook owns the raw input backings and the one pass-local Eq
/// allocation alongside the descriptor that references them.
pub(crate) fn bind_dr_window_r0<B>(
    program: &DrWindowProgram,
    projection: &DrWindowInputProjection,
    storage: &GpuGKRStorage<B, E4>,
    folding_steps: usize,
    eq: DrWindowPassEqState,
    scratch: DrWindowRuntimeScratch,
) -> Result<DrWindowLayerCompositionHook, DrWindowBindError> {
    let raw_inputs = DrWindowRawInputKeepalive::from_projection(storage, projection)?;
    let partials_capacity = scratch.partials_capacity;
    let launch = bind_dr_window_launch(program, storage, folding_steps, &eq, scratch)?;
    Ok(DrWindowLayerCompositionHook::new(
        launch,
        eq,
        raw_inputs,
        partials_capacity,
    ))
}

/// Prepare the allocation-neutral Task 6 seam. The caller supplies a typed
/// view of the common round Eq owner and checked metadata for the future
/// complete-chain scratch requirement; no runtime scratch pointer is accepted.
pub(crate) fn prepare_dr_window_r0<B>(
    program: &DrWindowProgram,
    projection: &DrWindowInputProjection,
    storage: &GpuGKRStorage<B, E4>,
    folding_steps: usize,
    eq: DrWindowPassEqView,
    required_future_partials_len: usize,
) -> Result<DrWindowLayerPreparationHook, DrWindowBindError> {
    validate_dr_window_folding_steps(folding_steps)?;
    let kernel = resolve_dr_window_kernel(program.enabled_mask())?;
    validate_dr_r0_eq_contract(folding_steps, eq.build_offset, eq.eq_sizes)?;
    let expected_partials_len = dr_window_partials_len(folding_steps);
    assert_eq!(
        required_future_partials_len, expected_partials_len,
        "Task 6 must retain the exact future complete-chain partials requirement as metadata",
    );
    let raw_inputs = DrWindowRawInputKeepalive::from_projection(storage, projection)?;
    let row_tiles = dr_window_row_tiles(folding_steps);
    let batch = build_dr_window_batch(program, storage, eq)?;
    assert_eq!(
        batch.eq_low, eq.eq_low,
        "the prepared descriptor must borrow its non-owning Eq view",
    );
    Ok(DrWindowLayerPreparationHook::new(
        DrWindowR0Preparation {
            batch,
            kernel,
            row_tiles,
            folding_steps,
            required_future_partials_len,
        },
        eq,
        raw_inputs,
    ))
}

impl KernelFunction for DrWindowKernelEntry {
    type Signature = GkrDrR0Window3Signature;

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
