//! Runtime storage binding for the width-three MAIN continuation window.

use core::marker::PhantomData;
use core::mem::size_of;

use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::{
    MainContinuationWindowProgram, MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY,
    MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY, MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY,
    SOURCE_WINDOW_COLUMNS,
};
use gpu_prover_context::ProverContext;

use super::abi::{
    MainContinuationWindowSourceRecord, MAIN_CONTINUATION_WINDOW_FOLD_COORDINATES,
    MAIN_CONTINUATION_WINDOW_PUBLICATION_BLOCKS_PER_TILE, MAIN_CONTINUATION_WINDOW_ROWS_PER_TILE,
    MAIN_CONTINUATION_WINDOW_SELECTOR_BLOCKS, MAIN_CONTINUATION_WINDOW_TENSOR_CELLS,
    MAIN_CONTINUATION_WINDOW_WARPS,
};
use super::{ContinuationPublicationError, ContinuationPublishedLevel, ContinuationPublishedShape};
use crate::backward::make_eq_sizes;
use crate::backward::window::bank::family_read_place;
use crate::backward::window::common::{
    bwd_source_lane, BwdSourceWindow, BWD_COEFF_NONE, BWD_COEFF_ORIGIN_PROCEDURAL,
    BWD_COEFF_ORIGIN_READ_BASE, BWD_COEFF_ORIGIN_READ_EXT, BWD_COEFF_PROCEDURAL_NONE,
    BWD_SOURCE_WINDOW_SLOTS,
};
use crate::backward::window::zeroed_box;
use crate::backward::GkrEqSizes;
use crate::forward::vm::lower::read_place_to_gkr_address;
use crate::forward::vm::production_bind::resolve_storage_column;
use crate::upstream::PrimeField;
use crate::GpuGKRStorage;

pub(crate) use super::abi::MainContinuationWindowDesc as MainContinuationWindowLaunchBinding;

#[path = "dispatch.rs"]
mod dispatch;
pub(crate) use dispatch::launch_main_continuation_window;
use dispatch::{select_dispatch, WindowDispatch};

// Recomputed delegation inputs need up to 23 first-window slots. Reserve
// headroom within the existing 64-slot descriptor; the wire ABI is unchanged.
const FIRST_WINDOW_ADDR_SLOT_MAX: usize = 32;
const LATER_WINDOW_ADDR_SLOT_MAX: usize = 16;
const _: () = assert!(FIRST_WINDOW_ADDR_SLOT_MAX <= BWD_SOURCE_WINDOW_SLOTS);
const _: () = assert!(LATER_WINDOW_ADDR_SLOT_MAX <= BWD_SOURCE_WINDOW_SLOTS);

#[derive(Debug)]
pub(crate) enum MainContinuationWindowBindError {
    Cuda(era_cudart_sys::CudaError),
    Publication(ContinuationPublicationError),
    NoKernelForMask {
        mask: u16,
    },
    InvalidGeometry {
        folding_steps: usize,
        start_round: usize,
    },
    Capacity {
        resource: &'static str,
        required: usize,
        capacity: usize,
    },
    UnresolvedRawSource {
        source: u32,
    },
    RawSourceFieldMismatch {
        source: u32,
        expect_e4: bool,
    },
    RawSourceStrideMismatch {
        source: u32,
        stride_bytes: u32,
    },
    RawSourceRankMismatch {
        source: u32,
    },
    SourceAlignment {
        source: u32,
        address: usize,
    },
    ArenaAlignment {
        address: usize,
        column_elems: usize,
    },
    UnknownProceduralKind {
        source: u32,
        kind: u8,
    },
    NullRuntimePointer {
        resource: &'static str,
    },
    PriorShapeMismatch {
        expected: ContinuationPublishedShape,
        actual: ContinuationPublishedShape,
    },
    InputOutputAlias,
    FoldListDuplicate {
        source: u16,
    },
    FoldListMissing {
        source: u16,
    },
}

impl From<era_cudart_sys::CudaError> for MainContinuationWindowBindError {
    fn from(error: era_cudart_sys::CudaError) -> Self {
        Self::Cuda(error)
    }
}

impl From<ContinuationPublicationError> for MainContinuationWindowBindError {
    fn from(error: ContinuationPublicationError) -> Self {
        Self::Publication(error)
    }
}

impl core::fmt::Display for MainContinuationWindowBindError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Cuda(error) => write!(formatter, "CUDA error: {error:?}"),
            Self::Publication(error) => write!(formatter, "publication: {error}"),
            Self::NoKernelForMask { mask } => write!(formatter, "no kernel for mask {mask:#x}"),
            Self::InvalidGeometry {
                folding_steps,
                start_round,
            } => write!(
                formatter,
                "invalid geometry: {folding_steps} folding steps, start round {start_round}"
            ),
            Self::Capacity {
                resource,
                required,
                capacity,
            } => write!(
                formatter,
                "{resource} needs {required}, capacity {capacity}"
            ),
            Self::UnresolvedRawSource { source } => write!(formatter, "unresolved source {source}"),
            Self::RawSourceFieldMismatch { source, expect_e4 } => {
                write!(
                    formatter,
                    "source {source} extension-field expectation is {expect_e4}"
                )
            }
            Self::RawSourceStrideMismatch {
                source,
                stride_bytes,
            } => write!(formatter, "source {source} has stride {stride_bytes}"),
            Self::RawSourceRankMismatch { source } => {
                write!(formatter, "source {source} has invalid rank")
            }
            Self::SourceAlignment { source, address } => {
                write!(
                    formatter,
                    "source {source} has unaligned address {address:#x}"
                )
            }
            Self::ArenaAlignment {
                address,
                column_elems,
            } => write!(
                formatter,
                "arena {address:#x} is unaligned for {column_elems}-element columns"
            ),
            Self::UnknownProceduralKind { source, kind } => {
                write!(
                    formatter,
                    "source {source} has unknown procedural kind {kind}"
                )
            }
            Self::NullRuntimePointer { resource } => write!(formatter, "null {resource} pointer"),
            Self::PriorShapeMismatch { expected, actual } => {
                write!(formatter, "prior shape {actual:?}, expected {expected:?}")
            }
            Self::InputOutputAlias => formatter.write_str("input aliases output"),
            Self::FoldListDuplicate { source } => {
                write!(formatter, "duplicate fold source {source}")
            }
            Self::FoldListMissing { source } => write!(formatter, "missing fold source {source}"),
        }
    }
}

impl std::error::Error for MainContinuationWindowBindError {}

#[derive(Clone, Copy, Debug)]
pub(crate) struct MainContinuationWindowRuntimeScratch {
    pub(crate) eq_low: *const E4,
    pub(crate) partials: *mut E4,
    pub(crate) partials_capacity: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MainContinuationInputKind {
    First,
    Later,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MainContinuationLaunchKind {
    R0Publication,
    Continuation { start_round: usize },
}

impl MainContinuationInputKind {
    fn address_slot_max(self) -> usize {
        match self {
            Self::First => FIRST_WINDOW_ADDR_SLOT_MAX,
            Self::Later => LATER_WINDOW_ADDR_SLOT_MAX,
        }
    }
}

/// Prepared launch. The lifetime is tied to raw storage or the prior published
/// level, so its input owner cannot be dropped before the kernel is enqueued.
pub(crate) struct MainContinuationWindowLaunch<'input> {
    binding: Box<MainContinuationWindowLaunchBinding>,
    dispatch: WindowDispatch,
    published: ContinuationPublishedLevel,
    row_tiles: usize,
    publication_grid_blocks: u32,
    grid_blocks: u32,
    reduced_tensor: *mut E4,
    _input_keepalive: PhantomData<&'input ()>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FoldItem {
    source: u16,
    byte_weight: usize,
}

fn build_fold_lists(
    items: impl IntoIterator<Item = FoldItem>,
    source_count: usize,
    require_all: bool,
) -> Result<([u16; MAIN_CONTINUATION_WINDOW_WARPS + 1], Vec<u16>), MainContinuationWindowBindError>
{
    let mut items: Vec<_> = items.into_iter().collect();
    items.sort_unstable_by_key(|item| (core::cmp::Reverse(item.byte_weight), item.source));
    let mut loads = [0usize; MAIN_CONTINUATION_WINDOW_WARPS];
    let mut lists: [Vec<u16>; MAIN_CONTINUATION_WINDOW_WARPS] = std::array::from_fn(|_| Vec::new());
    for item in items {
        let warp = (0..MAIN_CONTINUATION_WINDOW_WARPS)
            .min_by_key(|warp| (loads[*warp], *warp))
            .expect("the continuation executor has nine warps");
        loads[warp] += item.byte_weight;
        lists[warp].push(item.source);
    }

    let mut offsets = [0u16; MAIN_CONTINUATION_WINDOW_WARPS + 1];
    let mut flattened = Vec::with_capacity(source_count);
    for (warp, list) in lists.into_iter().enumerate() {
        flattened.extend(list);
        offsets[warp + 1] = u16::try_from(flattened.len()).map_err(|_| {
            MainContinuationWindowBindError::Capacity {
                resource: "fold sources",
                required: flattened.len(),
                capacity: u16::MAX as usize,
            }
        })?;
    }

    let mut seen = vec![false; source_count];
    for &source in &flattened {
        let source_index = usize::from(source);
        if source_index >= source_count || seen[source_index] {
            return Err(MainContinuationWindowBindError::FoldListDuplicate { source });
        }
        seen[source_index] = true;
    }
    if let Some(source) = seen.iter().position(|present| require_all && !present) {
        return Err(MainContinuationWindowBindError::FoldListMissing {
            source: source as u16,
        });
    }
    Ok((offsets, flattened))
}

fn window_grid_blocks(
    row_tiles: usize,
    blocks_per_tile: usize,
) -> Result<u32, MainContinuationWindowBindError> {
    let required = row_tiles.checked_mul(blocks_per_tile).ok_or(
        MainContinuationWindowBindError::Capacity {
            resource: "grid blocks",
            required: usize::MAX,
            capacity: u32::MAX as usize,
        },
    )?;
    u32::try_from(required).map_err(|_| MainContinuationWindowBindError::Capacity {
        resource: "grid blocks",
        required,
        capacity: u32::MAX as usize,
    })
}

#[derive(Clone, Copy)]
struct AddressSlotTable {
    slots: [BwdSourceWindow; BWD_SOURCE_WINDOW_SLOTS],
    len: usize,
}

impl AddressSlotTable {
    fn new() -> Self {
        // SAFETY: null base, zero stride/origin/kind and zero reserved bytes are
        // a valid inert address slot. Only the leading `len` entries are copied.
        Self {
            slots: unsafe { core::mem::zeroed() },
            len: 0,
        }
    }

    fn intern(&mut self, slot: BwdSourceWindow) -> Result<usize, MainContinuationWindowBindError> {
        if let Some(index) = self.slots[..self.len].iter().position(|entry| {
            entry.base == slot.base
                && entry.log2_stride == slot.log2_stride
                && entry.origin == slot.origin
                && entry.procedural_kind == slot.procedural_kind
        }) {
            return Ok(index);
        }
        if self.len == self.slots.len() {
            return Err(MainContinuationWindowBindError::Capacity {
                resource: "address slots",
                required: self.len + 1,
                capacity: self.slots.len(),
            });
        }
        let index = self.len;
        self.slots[index] = slot;
        self.len += 1;
        Ok(index)
    }

    fn lane(
        &mut self,
        slot: BwdSourceWindow,
        column: usize,
    ) -> Result<u16, MainContinuationWindowBindError> {
        let index = self.intern(slot)?;
        bwd_source_lane(index, column).ok_or(MainContinuationWindowBindError::Capacity {
            resource: "address lane column",
            required: column + 1,
            capacity: SOURCE_WINDOW_COLUMNS,
        })
    }
}

fn pointer_ranges_overlap(
    first: *const u8,
    first_bytes: usize,
    second: *const u8,
    second_bytes: usize,
) -> bool {
    let first_start = first as usize;
    let second_start = second as usize;
    let Some(first_end) = first_start.checked_add(first_bytes) else {
        return true;
    };
    let Some(second_end) = second_start.checked_add(second_bytes) else {
        return true;
    };
    first_start < second_end && second_start < first_end
}

fn checked_pow2(
    exponent: usize,
    folding_steps: usize,
    start_round: usize,
) -> Result<usize, MainContinuationWindowBindError> {
    if exponent >= usize::BITS as usize {
        return Err(MainContinuationWindowBindError::InvalidGeometry {
            folding_steps,
            start_round,
        });
    }
    1usize
        .checked_shl(exponent as u32)
        .ok_or(MainContinuationWindowBindError::InvalidGeometry {
            folding_steps,
            start_round,
        })
}

fn publication_shape(
    program: &MainContinuationWindowProgram,
    folding_steps: usize,
    start_round: usize,
) -> Result<(ContinuationPublishedShape, usize, usize), MainContinuationWindowBindError> {
    if start_round < MAIN_CONTINUATION_WINDOW_FOLD_COORDINATES
        || !start_round.is_multiple_of(MAIN_CONTINUATION_WINDOW_FOLD_COORDINATES)
        || folding_steps < start_round + MAIN_CONTINUATION_WINDOW_FOLD_COORDINATES
        || start_round > u8::MAX as usize
    {
        return Err(MainContinuationWindowBindError::InvalidGeometry {
            folding_steps,
            start_round,
        });
    }
    let suffix_coordinates =
        folding_steps - start_round - MAIN_CONTINUATION_WINDOW_FOLD_COORDINATES;
    let logical_rows = checked_pow2(suffix_coordinates, folding_steps, start_round)?;
    let column_elems =
        logical_rows
            .checked_mul(8)
            .ok_or(MainContinuationWindowBindError::InvalidGeometry {
                folding_steps,
                start_round,
            })?;
    let row_tiles = logical_rows.div_ceil(MAIN_CONTINUATION_WINDOW_ROWS_PER_TILE);
    Ok((
        ContinuationPublishedShape {
            depth: start_round as u8,
            columns: program.sources.len(),
            column_elems,
        },
        logical_rows,
        row_tiles,
    ))
}

fn r0_publication_shape(
    program: &MainContinuationWindowProgram,
    folding_steps: usize,
) -> Result<(ContinuationPublishedShape, usize, usize), MainContinuationWindowBindError> {
    if folding_steps < MAIN_CONTINUATION_WINDOW_FOLD_COORDINATES || folding_steps > u8::MAX as usize
    {
        return Err(MainContinuationWindowBindError::InvalidGeometry {
            folding_steps,
            start_round: 0,
        });
    }
    let logical_rows = checked_pow2(
        folding_steps - MAIN_CONTINUATION_WINDOW_FOLD_COORDINATES,
        folding_steps,
        0,
    )?;
    let column_elems =
        logical_rows
            .checked_mul(8)
            .ok_or(MainContinuationWindowBindError::InvalidGeometry {
                folding_steps,
                start_round: 0,
            })?;
    Ok((
        ContinuationPublishedShape {
            depth: 0,
            columns: program.sources.len(),
            column_elems,
        },
        logical_rows,
        logical_rows.div_ceil(MAIN_CONTINUATION_WINDOW_ROWS_PER_TILE),
    ))
}

fn append_canonical_arena_slots(
    table: &mut AddressSlotTable,
    base: *const E4,
    column_elems: usize,
    columns: usize,
) -> Result<Vec<u16>, MainContinuationWindowBindError> {
    if !column_elems.is_power_of_two() || !(base as usize).is_multiple_of(32) {
        return Err(MainContinuationWindowBindError::ArenaAlignment {
            address: base as usize,
            column_elems,
        });
    }
    let mut lanes = Vec::with_capacity(columns);
    for source in 0..columns {
        let chunk = source / SOURCE_WINDOW_COLUMNS;
        let within = source % SOURCE_WINDOW_COLUMNS;
        let chunk_elems = chunk
            .checked_mul(SOURCE_WINDOW_COLUMNS)
            .and_then(|value| value.checked_mul(column_elems))
            .ok_or(MainContinuationWindowBindError::Capacity {
                resource: "canonical arena offset",
                required: usize::MAX,
                capacity: usize::MAX - 1,
            })?;
        let slot = BwdSourceWindow {
            base: base.wrapping_add(chunk_elems).cast::<u8>(),
            log2_stride: column_elems.trailing_zeros() as u8,
            origin: BWD_COEFF_ORIGIN_READ_EXT,
            procedural_kind: BWD_COEFF_PROCEDURAL_NONE,
            reserved: 0,
            r0_stride_bytes: 0,
        };
        lanes.push(table.lane(slot, within)?);
    }
    Ok(lanes)
}

fn raw_input_lanes<E: Copy>(
    program: &MainContinuationWindowProgram,
    storage: &GpuGKRStorage<BF, E>,
    folding_steps: usize,
    destination: &ContinuationPublishedLevel,
    table: &mut AddressSlotTable,
) -> Result<(Vec<u16>, Vec<FoldItem>), MainContinuationWindowBindError> {
    let destination_bytes = destination
        .allocation()
        .len()
        .checked_mul(size_of::<E4>())
        .ok_or(MainContinuationWindowBindError::InputOutputAlias)?;
    let input_column_elems = checked_pow2(folding_steps, folding_steps, 3)?;
    let mut lanes = Vec::with_capacity(program.sources.len());
    let mut folds = Vec::with_capacity(program.sources.len());
    for (source_id, source) in program.sources.iter().enumerate() {
        if let gpu_gkr_compiler::WindowFamily::VirtualSetup { kind } = source.raw_family {
            if usize::from(kind) >= crate::backward::window::common::BWD_COEFF_PROCEDURAL_KINDS {
                return Err(MainContinuationWindowBindError::UnknownProceduralKind {
                    source: source_id as u32,
                    kind,
                });
            }
            let slot = BwdSourceWindow {
                base: core::ptr::null(),
                log2_stride: 0,
                origin: BWD_COEFF_ORIGIN_PROCEDURAL,
                procedural_kind: kind,
                reserved: 0,
                r0_stride_bytes: 0,
            };
            lanes.push(table.lane(slot, 0)?);
            folds.push(FoldItem {
                source: source_id as u16,
                byte_weight: 1,
            });
            continue;
        }
        let place = family_read_place(source.raw_family, source.raw_column).ok_or(
            MainContinuationWindowBindError::UnresolvedRawSource {
                source: source_id as u32,
            },
        )?;
        let resolved = resolve_storage_column(storage, read_place_to_gkr_address(&place)).ok_or(
            MainContinuationWindowBindError::UnresolvedRawSource {
                source: source_id as u32,
            },
        )?;
        let expect_e4 = matches!(
            source.raw_family,
            gpu_gkr_compiler::WindowFamily::LayerOutput { ext: true, .. }
                | gpu_gkr_compiler::WindowFamily::CacheOutput { ext: true, .. }
        );
        if resolved.is_e4 != expect_e4 {
            return Err(MainContinuationWindowBindError::RawSourceFieldMismatch {
                source: source_id as u32,
                expect_e4,
            });
        }
        let element_bytes = if expect_e4 {
            size_of::<E4>()
        } else {
            size_of::<BF>()
        };
        let stride_bytes = resolved.stride_bytes as usize;
        if !stride_bytes.is_multiple_of(element_bytes)
            || !(stride_bytes / element_bytes).is_power_of_two()
        {
            return Err(MainContinuationWindowBindError::RawSourceStrideMismatch {
                source: source_id as u32,
                stride_bytes: resolved.stride_bytes,
            });
        }
        let pointer = resolved.ptr as usize;
        let matrix = resolved.matrix_base as usize;
        if !pointer.is_multiple_of(32) {
            return Err(MainContinuationWindowBindError::SourceAlignment {
                source: source_id as u32,
                address: pointer,
            });
        }
        if pointer < matrix || !(pointer - matrix).is_multiple_of(stride_bytes) {
            return Err(MainContinuationWindowBindError::RawSourceRankMismatch {
                source: source_id as u32,
            });
        }
        let rank = (pointer - matrix) / stride_bytes;
        let chunk = rank / SOURCE_WINDOW_COLUMNS;
        let within = rank % SOURCE_WINDOW_COLUMNS;
        let chunk_base = matrix + chunk * SOURCE_WINDOW_COLUMNS * stride_bytes;
        let input_bytes = input_column_elems
            .checked_mul(element_bytes)
            .ok_or(MainContinuationWindowBindError::InputOutputAlias)?;
        if pointer_ranges_overlap(
            resolved.ptr,
            input_bytes,
            destination.as_ptr().cast::<u8>(),
            destination_bytes,
        ) {
            return Err(MainContinuationWindowBindError::InputOutputAlias);
        }
        let slot = BwdSourceWindow {
            base: chunk_base as *const u8,
            log2_stride: (stride_bytes / element_bytes).trailing_zeros() as u8,
            origin: if expect_e4 {
                BWD_COEFF_ORIGIN_READ_EXT
            } else {
                BWD_COEFF_ORIGIN_READ_BASE
            },
            procedural_kind: BWD_COEFF_PROCEDURAL_NONE,
            reserved: 0,
            r0_stride_bytes: 0,
        };
        lanes.push(table.lane(slot, within)?);
        folds.push(FoldItem {
            source: source_id as u16,
            byte_weight: if expect_e4 { 4 } else { 1 },
        });
    }
    Ok((lanes, folds))
}

fn prior_input_lanes(
    prior: &ContinuationPublishedLevel,
    expected: ContinuationPublishedShape,
    destination: &ContinuationPublishedLevel,
    table: &mut AddressSlotTable,
) -> Result<(Vec<u16>, Vec<FoldItem>), MainContinuationWindowBindError> {
    if prior.shape() != expected {
        return Err(MainContinuationWindowBindError::PriorShapeMismatch {
            expected,
            actual: prior.shape(),
        });
    }
    let prior_bytes = prior
        .allocation()
        .len()
        .checked_mul(size_of::<E4>())
        .ok_or(MainContinuationWindowBindError::InputOutputAlias)?;
    let destination_bytes = destination
        .allocation()
        .len()
        .checked_mul(size_of::<E4>())
        .ok_or(MainContinuationWindowBindError::InputOutputAlias)?;
    if pointer_ranges_overlap(
        prior.as_ptr().cast::<u8>(),
        prior_bytes,
        destination.as_ptr().cast::<u8>(),
        destination_bytes,
    ) {
        return Err(MainContinuationWindowBindError::InputOutputAlias);
    }
    let lanes = append_canonical_arena_slots(
        table,
        prior.as_ptr(),
        prior.shape().column_elems,
        prior.shape().columns,
    )?;
    let folds = (0..expected.columns)
        .map(|source| FoldItem {
            source: source as u16,
            byte_weight: 4,
        })
        .collect();
    Ok((lanes, folds))
}

fn encode_main_continuation_immediate_prefix(canonical: &[u32], destination: &mut [u32]) {
    for (encoded, &value) in destination[..canonical.len()].iter_mut().zip(canonical) {
        *encoded = BF::from_u32_with_reduction(value).as_u32_raw_repr_reduced();
    }
}

#[allow(clippy::too_many_arguments)]
fn assemble_launch<'input>(
    program: &MainContinuationWindowProgram,
    folding_steps: usize,
    launch_kind: MainContinuationLaunchKind,
    scratch: MainContinuationWindowRuntimeScratch,
    context: &ProverContext,
    input_kind: MainContinuationInputKind,
    input_lanes: impl FnOnce(
        &ContinuationPublishedLevel,
        &mut AddressSlotTable,
    ) -> Result<(Vec<u16>, Vec<FoldItem>), MainContinuationWindowBindError>,
) -> Result<MainContinuationWindowLaunch<'input>, MainContinuationWindowBindError> {
    if scratch.eq_low.is_null() {
        return Err(MainContinuationWindowBindError::NullRuntimePointer { resource: "eq_low" });
    }
    if scratch.partials.is_null() {
        return Err(MainContinuationWindowBindError::NullRuntimePointer {
            resource: "partials",
        });
    }
    let (shape, _, row_tiles) = match launch_kind {
        MainContinuationLaunchKind::R0Publication => r0_publication_shape(program, folding_steps)?,
        MainContinuationLaunchKind::Continuation { start_round } => {
            publication_shape(program, folding_steps, start_round)?
        }
    };
    let grid_blocks = window_grid_blocks(row_tiles, MAIN_CONTINUATION_WINDOW_SELECTOR_BLOCKS)?;
    let publication_grid_blocks = window_grid_blocks(
        row_tiles,
        MAIN_CONTINUATION_WINDOW_PUBLICATION_BLOCKS_PER_TILE,
    )?;
    for (resource, required, capacity) in [
        (
            "program words",
            program.program.words.len(),
            MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY,
        ),
        (
            "semantic sources",
            program.sources.len(),
            MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY,
        ),
        (
            "immediates",
            program.immediates.len(),
            MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY,
        ),
    ] {
        if required > capacity {
            return Err(MainContinuationWindowBindError::Capacity {
                resource,
                required,
                capacity,
            });
        }
    }
    let required_partials = MAIN_CONTINUATION_WINDOW_TENSOR_CELLS
        .checked_mul(row_tiles + 1)
        .ok_or(MainContinuationWindowBindError::Capacity {
            resource: "partials",
            required: usize::MAX,
            capacity: scratch.partials_capacity,
        })?;
    if required_partials > scratch.partials_capacity {
        return Err(MainContinuationWindowBindError::Capacity {
            resource: "partials",
            required: required_partials,
            capacity: scratch.partials_capacity,
        });
    }

    let allocation = context.alloc(
        shape.columns.checked_mul(shape.column_elems).ok_or(
            MainContinuationWindowBindError::Capacity {
                resource: "publication elements",
                required: usize::MAX,
                capacity: usize::MAX - 1,
            },
        )?,
        AllocationPlacement::Top,
    )?;
    let published = ContinuationPublishedLevel::try_new(shape, allocation)?;

    let mut table = AddressSlotTable::new();
    let (read_lanes, folds) = input_lanes(&published, &mut table)?;
    let publish_lanes = append_canonical_arena_slots(
        &mut table,
        published.as_ptr(),
        shape.column_elems,
        shape.columns,
    )?;
    if table.len > input_kind.address_slot_max() {
        return Err(MainContinuationWindowBindError::Capacity {
            resource: match input_kind {
                MainContinuationInputKind::First => "first-window address slots",
                MainContinuationInputKind::Later => "later-window address slots",
            },
            required: table.len,
            capacity: input_kind.address_slot_max(),
        });
    }
    let (fold_list_offsets, fold_sources) = build_fold_lists(folds, shape.columns, true)?;

    // SAFETY: every descriptor field is valid at zero. Required pointers,
    // counts and live array prefixes are filled below before launch.
    let mut binding: Box<MainContinuationWindowLaunchBinding> = unsafe { zeroed_box() };
    let start_round = match launch_kind {
        MainContinuationLaunchKind::R0Publication => {
            binding.c_init_coeff = BWD_COEFF_NONE;
            0
        }
        MainContinuationLaunchKind::Continuation { start_round } => {
            binding.program[..program.program.words.len()].copy_from_slice(&program.program.words);
            binding.program_words = program.program.words.len() as u16;
            binding.c_init_coeff = program
                .c_init
                .map_or(BWD_COEFF_NONE, |coefficient| coefficient.0);
            encode_main_continuation_immediate_prefix(&program.immediates, &mut binding.immediates);
            binding.publication_fold = MAIN_CONTINUATION_WINDOW_FOLD_COORDINATES as u32;
            start_round
        }
    };
    binding.source_count = shape.columns as u16;
    binding.fold_list_offsets = fold_list_offsets;
    binding.fold_sources[..fold_sources.len()].copy_from_slice(&fold_sources);
    for source in 0..shape.columns {
        binding.source[source] = MainContinuationWindowSourceRecord {
            src: read_lanes[source],
            publish: publish_lanes[source],
        };
    }
    binding.slot[..table.len].copy_from_slice(&table.slots[..table.len]);
    binding.eq_low = scratch.eq_low;
    binding.partials = scratch.partials;
    binding.row_tiles =
        u32::try_from(row_tiles).map_err(|_| MainContinuationWindowBindError::Capacity {
            resource: "row tiles",
            required: row_tiles,
            capacity: u32::MAX as usize,
        })?;
    binding.eq_sizes =
        make_eq_sizes(folding_steps - start_round - MAIN_CONTINUATION_WINDOW_FOLD_COORDINATES);
    let dispatch = select_dispatch(
        program,
        &binding,
        input_kind,
        shape.column_elems / 8,
        context,
    )?;
    // SAFETY: the capacity check above reserves one trailing 27-cell tensor for
    // the unchanged tail's reduction scratch.
    let reduced_tensor = unsafe {
        scratch
            .partials
            .add(MAIN_CONTINUATION_WINDOW_TENSOR_CELLS * row_tiles)
    };
    Ok(MainContinuationWindowLaunch {
        dispatch,
        binding,
        published,
        row_tiles,
        publication_grid_blocks,
        grid_blocks,
        reduced_tensor,
        _input_keepalive: PhantomData,
    })
}

pub(crate) fn bind_first_main_continuation_window<'input, E: Copy>(
    program: &MainContinuationWindowProgram,
    storage: &'input GpuGKRStorage<BF, E>,
    folding_steps: usize,
    start_round: usize,
    scratch: MainContinuationWindowRuntimeScratch,
    context: &ProverContext,
) -> Result<MainContinuationWindowLaunch<'input>, MainContinuationWindowBindError> {
    if start_round != MAIN_CONTINUATION_WINDOW_FOLD_COORDINATES {
        return Err(MainContinuationWindowBindError::InvalidGeometry {
            folding_steps,
            start_round,
        });
    }
    assemble_launch(
        program,
        folding_steps,
        MainContinuationLaunchKind::Continuation { start_round },
        scratch,
        context,
        MainContinuationInputKind::First,
        |destination, table| raw_input_lanes(program, storage, folding_steps, destination, table),
    )
}

pub(crate) fn bind_main_r0_publication<'input, E: Copy>(
    program: &MainContinuationWindowProgram,
    storage: &'input GpuGKRStorage<BF, E>,
    folding_steps: usize,
    scratch: MainContinuationWindowRuntimeScratch,
    context: &ProverContext,
) -> Result<MainContinuationWindowLaunch<'input>, MainContinuationWindowBindError> {
    assemble_launch(
        program,
        folding_steps,
        MainContinuationLaunchKind::R0Publication,
        scratch,
        context,
        MainContinuationInputKind::First,
        |destination, table| raw_input_lanes(program, storage, folding_steps, destination, table),
    )
}

pub(crate) fn bind_later_main_continuation_window<'input>(
    program: &MainContinuationWindowProgram,
    prior: &'input ContinuationPublishedLevel,
    folding_steps: usize,
    start_round: usize,
    scratch: MainContinuationWindowRuntimeScratch,
    context: &ProverContext,
) -> Result<MainContinuationWindowLaunch<'input>, MainContinuationWindowBindError> {
    let prior_shape = publication_shape(program, folding_steps, start_round)?.0;
    let expected = ContinuationPublishedShape {
        depth: prior_shape.depth - 3,
        columns: prior_shape.columns,
        column_elems: prior_shape.column_elems.checked_mul(8).ok_or(
            MainContinuationWindowBindError::InvalidGeometry {
                folding_steps,
                start_round,
            },
        )?,
    };
    assemble_launch(
        program,
        folding_steps,
        MainContinuationLaunchKind::Continuation { start_round },
        scratch,
        context,
        MainContinuationInputKind::Later,
        |destination, table| prior_input_lanes(prior, expected, destination, table),
    )
}
