//! Runtime binding and enqueue-only launch for the dedicated width-three main
//! continuation window.

use core::marker::PhantomData;
use core::mem::size_of;

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::{
    MainContinuationWindowProgram, MainContinuationWindowShape,
    MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY, MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY,
    MAIN_CONTINUATION_WINDOW_SHAPE_DEFINED_BITS, MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY,
    SOURCE_WINDOW_COLUMNS,
};
use gpu_prover_context::ProverContext;

use super::abi::{
    MainContinuationWindowSourceRecord, MAIN_CONTINUATION_WINDOW_FOLD_COORDINATES,
    MAIN_CONTINUATION_WINDOW_PUBLICATION_BLOCKS_PER_TILE,
    MAIN_CONTINUATION_WINDOW_PUBLICATION_THREADS, MAIN_CONTINUATION_WINDOW_ROWS_PER_TILE,
    MAIN_CONTINUATION_WINDOW_SELECTOR_BLOCKS, MAIN_CONTINUATION_WINDOW_TENSOR_CELLS,
    MAIN_CONTINUATION_WINDOW_WARPS,
};
use super::generated_registry::{
    GkrBwdMainContinuationWindow3Arguments, GkrBwdMainContinuationWindow3Signature,
    MainContinuationWindowKernelEntry, MAIN_CONTINUATION_WINDOW_BLOCK_THREADS,
    MAIN_CONTINUATION_WINDOW_FALLBACK_MASK, MAIN_CONTINUATION_WINDOW_KERNELS,
};
use super::{ContinuationPublicationError, ContinuationPublishedLevel, ContinuationPublishedShape};
use crate::backward::make_eq_sizes;
use crate::backward::vm::production_bind::family_read_place;
use crate::backward::vm::seg_desc::{
    bwd_seg_lane, BwdSegAddrSlot, BWD_COEFF_ORIGIN_PROCEDURAL, BWD_COEFF_ORIGIN_READ_BASE,
    BWD_COEFF_ORIGIN_READ_EXT, BWD_COEFF_PROCEDURAL_NONE, BWD_SEG_ADDR_SLOTS, BWD_SEG_C_INIT_NONE,
};
use crate::backward::vm::seg_lower::zeroed_box;
use crate::backward::GkrEqSizes;
use crate::forward::vm::lower::read_place_to_gkr_address;
use crate::forward::vm::production_bind::resolve_storage_column;
use crate::upstream::PrimeField;
use crate::GpuGKRStorage;

pub(crate) use super::abi::MainContinuationWindowDesc as MainContinuationWindowLaunchBinding;

const FIRST_WINDOW_ADDR_SLOT_MAX: usize = 22;
const LATER_WINDOW_ADDR_SLOT_MAX: usize = 16;
const MAIN_CONTINUATION_WINDOW_X01_PROGRAM_WORD_THRESHOLD: usize = 5_500;

#[derive(Debug)]
pub(crate) enum MainContinuationWindowBindError {
    Cuda(era_cudart_sys::CudaError),
    Publication(ContinuationPublicationError),
    UndefinedShapeBits {
        bits: u16,
    },
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
    NonCanonicalSource {
        position: usize,
        semantic_id: u32,
        publish_column: u16,
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
        write!(formatter, "{self:?}")
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
    publish_kernel: MainContinuationWindowPublicationKernel,
    kernel: MainContinuationWindowEvaluatorKernel,
    published: ContinuationPublishedLevel,
    row_tiles: usize,
    publication_grid_blocks: u32,
    grid_blocks: u32,
    reduced_tensor: *mut E4,
    _input_keepalive: PhantomData<&'input ()>,
}

impl MainContinuationWindowLaunch<'_> {
    pub(crate) fn is_continuation_window(&self) -> bool {
        self.binding.publication_fold == MAIN_CONTINUATION_WINDOW_FOLD_COORDINATES as u32
    }
}

/// Output ownership returned only after the reader launch has been enqueued.
pub(crate) struct MainContinuationWindowLaunched {
    published: ContinuationPublishedLevel,
    row_tiles: usize,
    reduced_tensor: *mut E4,
    eq_sizes: GkrEqSizes,
}

impl MainContinuationWindowLaunched {
    pub(crate) fn published_level(&self) -> &ContinuationPublishedLevel {
        &self.published
    }

    pub(crate) fn into_published_level(self) -> ContinuationPublishedLevel {
        self.published
    }

    pub(crate) fn row_tiles(&self) -> usize {
        self.row_tiles
    }

    pub(crate) fn reduced_tensor(&self) -> *mut E4 {
        self.reduced_tensor
    }

    /// Exact pass-local Eq shape copied from the enqueued descriptor. The
    /// physical tail advances this host mirror once before boundary checking.
    pub(crate) fn eq_sizes(&self) -> GkrEqSizes {
        self.eq_sizes
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FoldItem {
    source: u16,
    byte_weight: usize,
}

fn build_lpt_fold_lists(
    items: impl IntoIterator<Item = FoldItem>,
    source_count: usize,
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
    if let Some(source) = seen.iter().position(|present| !present) {
        return Err(MainContinuationWindowBindError::FoldListMissing {
            source: source as u16,
        });
    }
    Ok((offsets, flattened))
}

fn main_continuation_window_grid_blocks(
    row_tiles: usize,
) -> Result<u32, MainContinuationWindowBindError> {
    let required = row_tiles
        .checked_mul(MAIN_CONTINUATION_WINDOW_SELECTOR_BLOCKS)
        .ok_or(MainContinuationWindowBindError::Capacity {
            resource: "grid blocks",
            required: usize::MAX,
            capacity: u32::MAX as usize,
        })?;
    u32::try_from(required).map_err(|_| MainContinuationWindowBindError::Capacity {
        resource: "grid blocks",
        required,
        capacity: u32::MAX as usize,
    })
}

fn main_continuation_window_publication_grid_blocks(
    row_tiles: usize,
) -> Result<u32, MainContinuationWindowBindError> {
    let blocks = row_tiles
        .checked_mul(MAIN_CONTINUATION_WINDOW_PUBLICATION_BLOCKS_PER_TILE)
        .ok_or(MainContinuationWindowBindError::Capacity {
            resource: "publication grid blocks",
            required: usize::MAX,
            capacity: u32::MAX as usize,
        })?;
    u32::try_from(blocks).map_err(|_| MainContinuationWindowBindError::Capacity {
        resource: "publication grid blocks",
        required: blocks,
        capacity: u32::MAX as usize,
    })
}

fn resolve_kernel(
    shape: MainContinuationWindowShape,
) -> Result<&'static MainContinuationWindowKernelEntry, MainContinuationWindowBindError> {
    let mask = shape.bits();
    if mask & !MAIN_CONTINUATION_WINDOW_SHAPE_DEFINED_BITS != 0 {
        return Err(MainContinuationWindowBindError::UndefinedShapeBits { bits: mask });
    }
    MAIN_CONTINUATION_WINDOW_KERNELS
        .iter()
        .find(|entry| entry.mask == mask)
        .or_else(|| {
            MAIN_CONTINUATION_WINDOW_KERNELS
                .iter()
                .find(|entry| entry.mask == MAIN_CONTINUATION_WINDOW_FALLBACK_MASK)
        })
        .ok_or(MainContinuationWindowBindError::NoKernelForMask { mask })
}

fn use_x01_specialization(program_words: usize) -> bool {
    program_words >= MAIN_CONTINUATION_WINDOW_X01_PROGRAM_WORD_THRESHOLD
}

#[derive(Clone, Copy)]
struct AddressSlotTable {
    slots: [BwdSegAddrSlot; BWD_SEG_ADDR_SLOTS],
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

    fn intern(&mut self, slot: BwdSegAddrSlot) -> Result<usize, MainContinuationWindowBindError> {
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
        slot: BwdSegAddrSlot,
        column: usize,
    ) -> Result<u16, MainContinuationWindowBindError> {
        let index = self.intern(slot)?;
        bwd_seg_lane(index, column).ok_or(MainContinuationWindowBindError::Capacity {
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

fn canonical_sources(
    program: &MainContinuationWindowProgram,
) -> Result<(), MainContinuationWindowBindError> {
    for (position, source) in program.sources.iter().enumerate() {
        if source.id.0 != position as u32 || usize::from(source.publish_column) != position {
            return Err(MainContinuationWindowBindError::NonCanonicalSource {
                position,
                semantic_id: source.id.0,
                publish_column: source.publish_column,
            });
        }
    }
    Ok(())
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
        let slot = BwdSegAddrSlot {
            base: base.wrapping_add(chunk_elems).cast::<u8>(),
            log2_stride: column_elems.trailing_zeros() as u8,
            origin: BWD_COEFF_ORIGIN_READ_EXT,
            procedural_kind: BWD_COEFF_PROCEDURAL_NONE,
            reserved: [0; 5],
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
    for source in &program.sources {
        if let gpu_gkr_compiler::WindowFamily::VirtualSetup { kind } = source.raw_family {
            if usize::from(kind) >= crate::backward::vm::seg_desc::BWD_COEFF_PROCEDURAL_KINDS {
                return Err(MainContinuationWindowBindError::UnknownProceduralKind {
                    source: source.id.0,
                    kind,
                });
            }
            let slot = BwdSegAddrSlot {
                base: core::ptr::null(),
                log2_stride: 0,
                origin: BWD_COEFF_ORIGIN_PROCEDURAL,
                procedural_kind: kind,
                reserved: [0; 5],
            };
            lanes.push(table.lane(slot, 0)?);
            folds.push(FoldItem {
                source: source.id.0 as u16,
                byte_weight: 1,
            });
            continue;
        }
        let place = family_read_place(source.raw_family, source.raw_column).ok_or(
            MainContinuationWindowBindError::UnresolvedRawSource {
                source: source.id.0,
            },
        )?;
        let resolved = resolve_storage_column(storage, read_place_to_gkr_address(&place)).ok_or(
            MainContinuationWindowBindError::UnresolvedRawSource {
                source: source.id.0,
            },
        )?;
        let expect_e4 = matches!(
            source.raw_family,
            gpu_gkr_compiler::WindowFamily::LayerOutput { ext: true, .. }
                | gpu_gkr_compiler::WindowFamily::CacheOutput { ext: true, .. }
        );
        if resolved.is_e4 != expect_e4 {
            return Err(MainContinuationWindowBindError::RawSourceFieldMismatch {
                source: source.id.0,
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
                source: source.id.0,
                stride_bytes: resolved.stride_bytes,
            });
        }
        let pointer = resolved.ptr as usize;
        let matrix = resolved.matrix_base as usize;
        if !pointer.is_multiple_of(32) {
            return Err(MainContinuationWindowBindError::SourceAlignment {
                source: source.id.0,
                address: pointer,
            });
        }
        if pointer < matrix || !(pointer - matrix).is_multiple_of(stride_bytes) {
            return Err(MainContinuationWindowBindError::RawSourceRankMismatch {
                source: source.id.0,
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
        let slot = BwdSegAddrSlot {
            base: chunk_base as *const u8,
            log2_stride: (stride_bytes / element_bytes).trailing_zeros() as u8,
            origin: if expect_e4 {
                BWD_COEFF_ORIGIN_READ_EXT
            } else {
                BWD_COEFF_ORIGIN_READ_BASE
            },
            procedural_kind: BWD_COEFF_PROCEDURAL_NONE,
            reserved: [0; 5],
        };
        lanes.push(table.lane(slot, within)?);
        folds.push(FoldItem {
            source: source.id.0 as u16,
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
    canonical_sources(program)?;
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
    let grid_blocks = main_continuation_window_grid_blocks(row_tiles)?;
    let publication_grid_blocks = main_continuation_window_publication_grid_blocks(row_tiles)?;
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
    let publication = program
        .sources
        .iter()
        .map(|source| (source.id, usize::from(source.publish_column)));
    let published = ContinuationPublishedLevel::try_new(shape, allocation, publication)?;

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
    let (fold_list_offsets, fold_sources) = build_lpt_fold_lists(folds, shape.columns)?;

    // SAFETY: every descriptor field is valid at zero. Required pointers,
    // counts and live array prefixes are filled below before launch.
    let mut binding: Box<MainContinuationWindowLaunchBinding> = unsafe { zeroed_box() };
    if matches!(launch_kind, MainContinuationLaunchKind::Continuation { .. }) {
        binding.program[..program.program.words.len()].copy_from_slice(&program.program.words);
        binding.program_words = program.program.words.len() as u16;
    }
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
    binding.c_init_coeff = match launch_kind {
        MainContinuationLaunchKind::R0Publication => BWD_SEG_C_INIT_NONE,
        MainContinuationLaunchKind::Continuation { .. } => program
            .c_init
            .map_or(BWD_SEG_C_INIT_NONE, |coefficient| coefficient.0),
    };
    if matches!(launch_kind, MainContinuationLaunchKind::Continuation { .. }) {
        encode_main_continuation_immediate_prefix(&program.immediates, &mut binding.immediates);
    }
    binding.publication_fold = match launch_kind {
        MainContinuationLaunchKind::R0Publication => 0,
        MainContinuationLaunchKind::Continuation { .. } => {
            MAIN_CONTINUATION_WINDOW_FOLD_COORDINATES as u32
        }
    };
    binding.eq_low = scratch.eq_low;
    binding.partials = scratch.partials;
    binding.row_tiles =
        u32::try_from(row_tiles).map_err(|_| MainContinuationWindowBindError::Capacity {
            resource: "row tiles",
            required: row_tiles,
            capacity: u32::MAX as usize,
        })?;
    binding.eq_sizes = make_eq_sizes(match launch_kind {
        MainContinuationLaunchKind::R0Publication => {
            folding_steps - MAIN_CONTINUATION_WINDOW_FOLD_COORDINATES
        }
        MainContinuationLaunchKind::Continuation { start_round } => {
            folding_steps - start_round - MAIN_CONTINUATION_WINDOW_FOLD_COORDINATES
        }
    });

    let kernel = resolve_kernel(program.shape)?;
    let evaluator_symbol = if use_x01_specialization(program.program.words.len()) {
        kernel.x01_symbol
    } else {
        kernel.symbol
    };
    // SAFETY: the capacity check above reserves one trailing 27-cell tensor for
    // the unchanged tail's reduction scratch.
    let reduced_tensor = unsafe {
        scratch
            .partials
            .add(MAIN_CONTINUATION_WINDOW_TENSOR_CELLS * row_tiles)
    };
    Ok(MainContinuationWindowLaunch {
        binding,
        publish_kernel: MainContinuationWindowPublicationKernel(kernel),
        kernel: MainContinuationWindowEvaluatorKernel(evaluator_symbol),
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

impl KernelFunction for MainContinuationWindowKernelEntry {
    type Signature = GkrBwdMainContinuationWindow3Signature;

    fn as_ptr(&self) -> *const std::os::raw::c_void {
        self.symbol as *const std::os::raw::c_void
    }
}

#[derive(Clone, Copy)]
struct MainContinuationWindowEvaluatorKernel(GkrBwdMainContinuationWindow3Signature);

impl KernelFunction for MainContinuationWindowEvaluatorKernel {
    type Signature = GkrBwdMainContinuationWindow3Signature;

    fn as_ptr(&self) -> *const std::os::raw::c_void {
        self.0 as *const std::os::raw::c_void
    }
}

#[derive(Clone, Copy)]
struct MainContinuationWindowPublicationKernel(&'static MainContinuationWindowKernelEntry);

impl KernelFunction for MainContinuationWindowPublicationKernel {
    type Signature = GkrBwdMainContinuationWindow3Signature;

    fn as_ptr(&self) -> *const std::os::raw::c_void {
        self.0.publication_symbol as *const std::os::raw::c_void
    }
}

/// Enqueue one prepared continuation window. Consuming the preparation keeps
/// its input borrow and output allocation alive through the CUDA launch call;
/// the owned canonical publication is returned only after enqueue succeeds.
pub(crate) fn launch_main_continuation_window(
    launch: MainContinuationWindowLaunch<'_>,
    context: &ProverContext,
) -> CudaResult<MainContinuationWindowLaunched> {
    let publication_config = CudaLaunchConfig::basic(
        launch.publication_grid_blocks,
        MAIN_CONTINUATION_WINDOW_PUBLICATION_THREADS,
        context.get_exec_stream(),
    );
    launch.publish_kernel.launch(
        &publication_config,
        &GkrBwdMainContinuationWindow3Arguments::new(*launch.binding),
    )?;
    let config = CudaLaunchConfig::basic(
        launch.grid_blocks,
        MAIN_CONTINUATION_WINDOW_BLOCK_THREADS,
        context.get_exec_stream(),
    );
    let eq_sizes = launch.binding.eq_sizes;
    launch.kernel.launch(
        &config,
        &GkrBwdMainContinuationWindow3Arguments::new(*launch.binding),
    )?;
    Ok(MainContinuationWindowLaunched {
        published: launch.published,
        row_tiles: launch.row_tiles,
        reduced_tensor: launch.reduced_tensor,
        eq_sizes,
    })
}

#[cfg(test)]
mod cpu_main_continuation_binding {
    use std::collections::BTreeSet;
    use std::path::PathBuf;

    use cs::gkr_compiler::GKRCircuitArtifact;
    use field::{FieldExtension, PrimeField};
    use gpu_gkr_compiler::{
        compile_continuations, interpret_main_continuation_window_shape,
        lower_main_continuation_window_program, CoeffResolver, CoefficientRecipeId, SourceId,
    };

    use super::*;

    type CpuBf = field::baby_bear::base::BabyBearField;
    type CpuExt = field::baby_bear::ext4::BabyBearExt4;

    struct Resolver;

    fn lift(value: u32) -> CpuExt {
        <CpuExt as FieldExtension<CpuBf>>::from_base(CpuBf::from_u32_with_reduction(value))
    }

    impl CoeffResolver for Resolver {
        fn coefficient(&self, id: CoefficientRecipeId) -> CpuExt {
            lift(13 + 17 * id.0)
        }

        fn source_pair(&self, id: SourceId, row: usize) -> (CpuExt, CpuExt) {
            let value = 29 + 19 * id.0 + 7 * row as u32;
            (lift(value), lift(value + 5))
        }
    }

    fn fold_items(weights: &[usize]) -> Vec<FoldItem> {
        weights
            .iter()
            .enumerate()
            .map(|(source, &byte_weight)| FoldItem {
                source: source as u16,
                byte_weight,
            })
            .collect()
    }

    #[test]
    fn cpu_r0_publication_geometry_is_depth_zero_for_every_zero_window_width() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../cs/compiled_circuits/blake2_with_extended_control_layout_gkr.json");
        let artifact: GKRCircuitArtifact<CpuBf> =
            serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        let dag = gkr_eval_ir::lower_dag(&artifact).unwrap();
        let source = compile_continuations(&dag)
            .unwrap()
            .layers
            .into_iter()
            .next()
            .unwrap();
        let program = lower_main_continuation_window_program(&source).unwrap();
        for folding_steps in 4usize..=6 {
            let (shape, logical_rows, row_tiles) =
                r0_publication_shape(&program, folding_steps).unwrap();
            assert_eq!(shape.depth, 0);
            assert_eq!(shape.columns, program.sources.len());
            assert_eq!(shape.column_elems, 1usize << folding_steps);
            assert_eq!(logical_rows, 1usize << (folding_steps - 3));
            assert_eq!(row_tiles, 1);
        }
        assert_ne!(
            r0_publication_shape(&program, 6).unwrap().0,
            publication_shape(&program, 6, 3).unwrap().0,
            "substituting the folded continuation publication must be detected"
        );
    }

    #[test]
    fn cpu_main_continuation_binding_lpt_is_deterministic_and_a_permutation() {
        let weights = [4, 1, 4, 1, 1, 4, 4, 1, 4, 1, 4, 1, 1, 4, 1, 4, 1, 4];
        let items = fold_items(&weights);
        let (offsets, flattened) = build_lpt_fold_lists(items.clone(), items.len()).unwrap();
        let (again_offsets, again) = build_lpt_fold_lists(items, flattened.len()).unwrap();
        assert_eq!((offsets, &flattened), (again_offsets, &again));
        let mut sorted = flattened.clone();
        sorted.sort_unstable();
        assert_eq!(sorted, (0..flattened.len() as u16).collect::<Vec<_>>());
        let loads: Vec<usize> = offsets
            .windows(2)
            .map(|bounds| {
                flattened[usize::from(bounds[0])..usize::from(bounds[1])]
                    .iter()
                    .map(|source| weights[usize::from(*source)])
                    .sum()
            })
            .collect();
        assert_eq!(loads.iter().copied().max(), Some(5));

        // Equal first jobs choose warp ids in ascending order. The tenth job
        // returns to warp 0, pinning both deterministic tie breaks.
        let (_, equal) = build_lpt_fold_lists(fold_items(&[1; 10]), 10).unwrap();
        assert_eq!(equal, vec![0, 9, 1, 2, 3, 4, 5, 6, 7, 8]);
    }

    #[test]
    fn cpu_main_continuation_binding_lpt_rejects_duplicate_and_missing_sources() {
        assert!(matches!(
            build_lpt_fold_lists(
                [
                    FoldItem {
                        source: 0,
                        byte_weight: 1,
                    },
                    FoldItem {
                        source: 0,
                        byte_weight: 4,
                    },
                ],
                2,
            ),
            Err(MainContinuationWindowBindError::FoldListDuplicate { source: 0 })
        ));
        assert!(matches!(
            build_lpt_fold_lists(
                [FoldItem {
                    source: 0,
                    byte_weight: 1,
                }],
                2,
            ),
            Err(MainContinuationWindowBindError::FoldListMissing { source: 1 })
        ));
    }

    #[test]
    fn cpu_main_continuation_binding_resolves_exact_masks_and_universal_fallback() {
        for entry in MAIN_CONTINUATION_WINDOW_KERNELS.iter() {
            let exact = MainContinuationWindowShape::from_bits(entry.mask).unwrap();
            assert_eq!(resolve_kernel(exact).unwrap().mask, entry.mask);
        }
        // 0x05 is well formed but absent from the seven-row corpus bank.
        let absent = MainContinuationWindowShape::from_bits(0x05).unwrap();
        assert_eq!(
            resolve_kernel(absent).unwrap().mask,
            MAIN_CONTINUATION_WINDOW_FALLBACK_MASK
        );
    }

    #[test]
    fn cpu_main_continuation_binding_selects_x01_only_for_long_programs() {
        assert!(!use_x01_specialization(
            MAIN_CONTINUATION_WINDOW_X01_PROGRAM_WORD_THRESHOLD - 1
        ));
        assert!(use_x01_specialization(
            MAIN_CONTINUATION_WINDOW_X01_PROGRAM_WORD_THRESHOLD
        ));
        assert!(!use_x01_specialization(4_977));
        assert!(use_x01_specialization(5_721));
        assert!(use_x01_specialization(6_468));
    }

    #[test]
    fn cpu_main_continuation_binding_exact_and_universal_executor_outputs_match() {
        const CORPUS: &[&str] = &[
            "add_sub_lui_auipc_mop_layout_gkr.json",
            "bigint_with_extended_control_layout_gkr.json",
            "blake2_g_function_layout_gkr.json",
            "blake2_with_extended_control_layout_gkr.json",
            "inits_and_teardowns_layout_gkr.json",
            "jump_branch_slt_layout_gkr.json",
            "keccak_special5_layout_gkr.json",
            "mem_subword_only_layout_gkr.json",
            "mem_word_only_layout_gkr.json",
            "shift_binop_layout_gkr.json",
            "unified_reduced_machine_layout_gkr.json",
            "unsigned_mul_div_layout_gkr.json",
        ];
        let directory =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
        let mut coordinates = 0usize;
        let mut masks = BTreeSet::new();
        for layout in CORPUS {
            let artifact: GKRCircuitArtifact<CpuBf> =
                serde_json::from_slice(&std::fs::read(directory.join(layout)).unwrap()).unwrap();
            let dag = gkr_eval_ir::lower_dag(&artifact).unwrap();
            let compiled = compile_continuations(&dag).unwrap();
            for source in compiled.layers {
                let program = lower_main_continuation_window_program(&source).unwrap();
                let exact_kernel = resolve_kernel(program.shape).unwrap();
                let universal_kernel = MAIN_CONTINUATION_WINDOW_KERNELS
                    .iter()
                    .find(|entry| entry.mask == MAIN_CONTINUATION_WINDOW_FALLBACK_MASK)
                    .unwrap();
                let exact = interpret_main_continuation_window_shape(
                    &program,
                    MainContinuationWindowShape::from_bits(exact_kernel.mask).unwrap(),
                    3,
                    &Resolver,
                    9,
                )
                .unwrap();
                let universal = interpret_main_continuation_window_shape(
                    &program,
                    MainContinuationWindowShape::from_bits(universal_kernel.mask).unwrap(),
                    3,
                    &Resolver,
                    9,
                )
                .unwrap();
                assert_eq!(exact, universal, "{layout} layer {}", program.layer);
                coordinates += 1;
                masks.insert(program.shape.bits());
            }
        }
        assert_eq!(coordinates, 57);
        assert_eq!(
            masks,
            BTreeSet::from([0x00, 0x01, 0x03, 0x07, 0x13, 0x17, 0x1f])
        );
    }

    #[test]
    fn cpu_main_continuation_immediate_encoding_matches_descriptor_abi() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../cs/compiled_circuits/mem_word_only_layout_gkr.json");
        let artifact: GKRCircuitArtifact<CpuBf> =
            serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        let dag = gkr_eval_ir::lower_dag(&artifact).unwrap();
        let compiled = compile_continuations(&dag).unwrap();
        let source = compiled.layers.first().expect("mem_word_only has layer 0");
        let program = lower_main_continuation_window_program(source).unwrap();

        assert_eq!(program.layer, 0);
        assert_eq!(program.shape, MainContinuationWindowShape::UNIVERSAL);
        assert_eq!(program.shape.bits(), 0x1f);
        assert_eq!(program.shape.bits(), MAIN_CONTINUATION_WINDOW_FALLBACK_MASK);
        assert_eq!(program.immediates.len(), 6);

        let expected = program
            .immediates
            .iter()
            .map(|&value| BF::from_u32_with_reduction(value).as_u32_raw_repr_reduced())
            .collect::<Vec<_>>();
        for (index, (&canonical, &raw)) in program.immediates.iter().zip(&expected).enumerate() {
            assert_ne!(canonical, raw, "immediate {index}");
        }

        let mut destination = [0u32; MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY];
        encode_main_continuation_immediate_prefix(&program.immediates, &mut destination);
        assert_eq!(
            &destination[..program.immediates.len()],
            expected.as_slice()
        );
        assert!(destination[program.immediates.len()..]
            .iter()
            .all(|&value| value == 0));
    }

    #[test]
    fn cpu_main_continuation_binding_geometry_pins_publication_and_tail_rows() {
        // This pure geometry check does not need a full compiler product.
        let logical_rows = checked_pow2(20 - 3 - 3, 20, 3).unwrap();
        assert_eq!(logical_rows, 1 << 14);
        assert_eq!(logical_rows.div_ceil(32), 512);
        assert_eq!(logical_rows * 8, 1 << 17);
        assert!(checked_pow2(usize::BITS as usize, usize::BITS as usize, 3).is_err());
    }

    #[test]
    fn cpu_main_continuation_binding_range_overlap_is_not_endpoint_only() {
        let base = 0x10_000usize as *const u8;
        assert!(pointer_ranges_overlap(
            base,
            128,
            base.wrapping_add(64),
            128
        ));
        assert!(!pointer_ranges_overlap(
            base,
            128,
            base.wrapping_add(128),
            64
        ));
    }

    #[test]
    fn cpu_main_continuation_binding_canonical_chunks_pin_later_slot_maximum() {
        let mut slots = AddressSlotTable::new();
        let input =
            append_canonical_arena_slots(&mut slots, 0x10_000usize as *const E4, 8_192, 1_012)
                .unwrap();
        assert_eq!(input.len(), 1_012);
        assert_eq!(slots.len, 8);
        let output =
            append_canonical_arena_slots(&mut slots, 0x1_0000_0000usize as *const E4, 1_024, 1_012)
                .unwrap();
        assert_eq!(output.len(), 1_012);
        assert_eq!(slots.len, LATER_WINDOW_ADDR_SLOT_MAX);
    }

    #[test]
    fn cpu_main_continuation_binding_native_contract_is_mutation_sensitive() {
        const EXECUTOR: &str =
            include_str!("../../../native/gkr/backward/main_continuation_window/executor.cuh");
        const PROLOGUE: &str =
            include_str!("../../../native/gkr/backward/main_continuation_window/fold_prologue.cuh");
        const ABI: &str = include_str!(
            "../../../native/gkr/backward/main_continuation_window/main_continuation_window_abi.cuh"
        );
        const BINDING: &str = include_str!("binding.rs");
        for required in [
            "bwd_main_cont_window_publish",
            "const u32 block_in_tile = blockIdx.x % BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCKS_PER_TILE;",
            "const u32 publication_partition = block_in_tile / BWD_MAIN_CONT_WINDOW_PUBLICATION_SUBBLOCKS_PER_TILE;",
            "const u32 publication_subblock = block_in_tile % BWD_MAIN_CONT_WINDOW_PUBLICATION_SUBBLOCKS_PER_TILE;",
            "const u32 publication_row_tile = blockIdx.x / BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCKS_PER_TILE;",
            "const u32 fold_warp = BWD_MAIN_CONT_WINDOW_BLOCK_WARPS * publication_partition + warp_id;",
            "const u32 row_in_block = lane / BWD_MAIN_CONT_WINDOW_PUBLICATION_LANES_PER_ROW;",
            "const u32 corner_pair = lane % BWD_MAIN_CONT_WINDOW_PUBLICATION_LANES_PER_ROW;",
            "bwd_main_cont_fold_prologue_pair(desc, fold_warp, active ? row : 0, active, corner_pair);",
            "const u32 row_tile = blockIdx.x / BWD_MAIN_CONT_WINDOW_SELECTOR_BLOCKS;",
            "template <u16 Shape, u32 X1, u32 X0>",
            "bwd_main_cont_resolve_source<X1, X0>",
            "const bool selector_boolean = X1 < 2 && (static_x0 ? X0 < 2 : dynamic_x0 < 2);",
            "const u32 cell = 9 * x2 + 3 * X1 + x0;",
            "bwd_main_cont_window_execute<Shape, X1, 0>(desc);",
            "bwd_main_cont_window_execute<Shape, X1, 1>(desc);",
            "bwd_main_cont_window_execute<Shape, X1, 2>(desc);",
            "AB_GKR_BWD_MAIN_CONT_WINDOW_DEFINE_X01_KERNEL",
            "desc.publication_fold != 0 && desc.publication_fold != 3",
            "desc.c_init_coeff != BWD_SEG_C_INIT_NONE",
            "BWD_MAIN_CONT_WINDOW_SHAPE_BANKED_GROUP_IMMEDIATE",
            "BWD_MAIN_CONT_WINDOW_SHAPE_NEGATIVE_GROUP_IMMEDIATE",
            "gkr_compute_eq_inline<e4>(desc.eq_low, desc.eq_sizes, safe_row)",
        ] {
            assert!(
                EXECUTOR.contains(required),
                "missing executor contract {required}"
            );
        }
        assert!(PROLOGUE.contains("store<bwd_main_cont_e4_pair, st_modifier::wb>"));
        assert!(PROLOGUE.contains("e4 outputs[2]"));
        assert!(PROLOGUE.contains("2 * corner_pair + offset"));
        assert!(!PROLOGUE.contains("e4 outputs[8]"));
        assert!(PROLOGUE.contains("desc.publication_fold == 0"));
        assert!(PROLOGUE.contains("gkr_virtual_base_value(kind, output_index)"));
        assert!(PROLOGUE.contains("e4::from_scalar(load<bf, ld_modifier::cs>"));
        assert!(PROLOGUE.contains("load<bwd_main_cont_bf8, ld_modifier::cs>"));
        assert!(PROLOGUE.contains("load<bwd_main_cont_e4_pair, ld_modifier::cs>"));
        assert!(!PROLOGUE.contains("fold_warp += BWD_MAIN_CONT_WINDOW_BLOCK_WARPS"));
        assert!(ABI.contains("BWD_MAIN_CONT_WINDOW_BLOCK_WARPS = 3"));
        assert!(ABI.contains("BWD_MAIN_CONT_WINDOW_SELECTOR_BLOCKS = 3"));
        assert!(ABI.contains("BWD_MAIN_CONT_WINDOW_BLOCK_THREADS = 96"));
        assert!(ABI.contains(
            "BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCK_THREADS = BWD_MAIN_CONT_WINDOW_BLOCK_WARPS * BWD_SEG_WARP_LANES"
        ));
        assert!(ABI.contains("BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCK_THREADS == 96"));
        assert!(ABI.contains("BWD_MAIN_CONT_WINDOW_PUBLICATION_LANES_PER_ROW == 4"));
        assert!(ABI.contains("BWD_MAIN_CONT_WINDOW_PUBLICATION_ROWS_PER_BLOCK == 8"));
        assert!(ABI.contains("BWD_MAIN_CONT_WINDOW_PUBLICATION_SUBBLOCKS_PER_TILE == 4"));
        assert!(ABI.contains("BWD_MAIN_CONT_WINDOW_PUBLICATION_BLOCKS_PER_TILE == 12"));
        assert!(ABI.contains("BWD_MAIN_CONT_WINDOW_DYNAMIC_X0 == 3"));
        assert!(BINDING
            .contains("program_words >= MAIN_CONTINUATION_WINDOW_X01_PROGRAM_WORD_THRESHOLD"));
        assert!(BINDING.contains("kernel.x01_symbol"));
        assert!(BINDING.contains(
            "launch.publication_grid_blocks,\n        MAIN_CONTINUATION_WINDOW_PUBLICATION_THREADS"
        ));
        let publication_launch = BINDING
            .find("launch.publish_kernel.launch")
            .expect("publication launch must use the selected generated kernel");
        let executor_launch = BINDING
            .find("launch.kernel.launch")
            .expect("executor launch must remain selected by shape");
        assert!(publication_launch < executor_launch);

        let selector_pairs = (0..3)
            .flat_map(|selector_block| (0..3).map(move |warp| 3 * selector_block + warp))
            .collect::<Vec<_>>();
        assert_eq!(selector_pairs, (0..9).collect::<Vec<_>>());
        let row_tiles = (0..6).map(|block| block / 3).collect::<Vec<_>>();
        assert_eq!(row_tiles, vec![0, 0, 0, 1, 1, 1]);
        assert_eq!(main_continuation_window_grid_blocks(7).unwrap(), 21);
        assert_eq!(
            main_continuation_window_publication_grid_blocks(7).unwrap(),
            84
        );
        let publication_rows = (0..12)
            .flat_map(|block| {
                let subblock = block % 4;
                (0..32).map(move |lane| subblock * 8 + lane / 4)
            })
            .collect::<Vec<_>>();
        let mut publication_row_counts = [0usize; 32];
        for row in publication_rows {
            publication_row_counts[row] += 1;
        }
        assert_eq!(publication_row_counts, [12; 32]);
        assert!(matches!(
            main_continuation_window_grid_blocks(u32::MAX as usize / 3 + 1),
            Err(MainContinuationWindowBindError::Capacity {
                resource: "grid blocks",
                ..
            })
        ));
        assert!(matches!(
            main_continuation_window_publication_grid_blocks(u32::MAX as usize / 12 + 1),
            Err(MainContinuationWindowBindError::Capacity {
                resource: "publication grid blocks",
                ..
            })
        ));
    }
}
