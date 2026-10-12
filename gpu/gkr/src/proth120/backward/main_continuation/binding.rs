use core::marker::PhantomData;
use core::mem::{align_of, offset_of, size_of};

use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_gkr_compiler::{
    MainContinuationWindowProgram, WindowFamily, DESCRIPTOR_ALIGNMENT_BYTES,
    KERNEL_ARGUMENT_CEILING_BYTES, LEAN_CLASS_SHIFT, LEAN_CONT_GROUP_HEADER_CLASS,
    LEAN_WORDS_PER_TERM, MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY,
    MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY, MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY,
    MAIN_CONTINUATION_WINDOW_SOURCE_WINDOW_CAPACITY, SOURCE_WINDOW_COLUMNS,
};
use gpu_prover_context::ProverContext;

use super::publication::ContinuationPublishedLevelPr;
use crate::backward::main_continuation::{
    ContinuationPublicationError, ContinuationPublishedShape,
};
use crate::backward::window::bank::family_read_place;
use crate::backward::window::common::{
    bwd_source_lane, BwdSourceWindow, BWD_COEFF_NONE, BWD_COEFF_ORIGIN_PROCEDURAL,
    BWD_COEFF_ORIGIN_READ_BASE, BWD_COEFF_ORIGIN_READ_EXT, BWD_COEFF_PROCEDURAL_KINDS,
    BWD_COEFF_PROCEDURAL_NONE, BWD_FOLD_WEIGHT_SLOTS, BWD_SOURCE_WINDOW_SLOTS,
};
use crate::backward::window::zeroed_box;
use crate::backward::{make_eq_sizes, GkrEqSizes};
use crate::forward::vm::lower::read_place_to_gkr_address;
use crate::proth120::backward::main_continuation_window_manifest::PrMainContinuationWindowKernelEntry;
use crate::proth120::forward::bind::resolve_storage_column;
use crate::upstream::PR;
use crate::GpuGKRStorage;

pub(crate) const PR_MAIN_CONTINUATION_BLOCK_THREADS: u32 = 96;
pub(crate) const PR_MAIN_CONTINUATION_FOLD_LISTS: usize = 3;
pub(crate) const PR_MAIN_CONTINUATION_ROWS_PER_TILE: usize = 32;
pub(crate) const PR_MAIN_CONTINUATION_TENSOR_CELLS: usize = 27;
pub(crate) const PR_MAIN_CONTINUATION_FOLD_COORDINATES: usize = 3;
pub(crate) const PR_MAIN_CONTINUATION_ARGUMENT_HEADROOM_BYTES: usize = 2_048;
const FIRST_WINDOW_ADDR_SLOT_MAX: usize = 32;
const LATER_WINDOW_ADDR_SLOT_MAX: usize = 16;
const CONTINUATION_ID_MASK: u16 = (1 << LEAN_CLASS_SHIFT) - 1;
const PROGRAM_IMMEDIATE_RESERVED: usize = 2;

#[repr(C, align(2))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct MainContinuationSourceRecordPr {
    pub(crate) src: u16,
    pub(crate) publish: u16,
}

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub(crate) struct MainContinuationWindowLaunchBindingPr {
    pub(crate) program: [u16; MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY],
    pub(crate) program_words: u16,
    pub(crate) source_count: u16,
    pub(crate) fold_list_offsets: [u16; PR_MAIN_CONTINUATION_FOLD_LISTS + 1],
    pub(crate) fold_sources: [u16; MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY],
    pub(crate) source: [MainContinuationSourceRecordPr; MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY],
    pub(crate) reserved0: [u16; 2],
    pub(crate) slot: [BwdSourceWindow; MAIN_CONTINUATION_WINDOW_SOURCE_WINDOW_CAPACITY],
    pub(crate) coefficients: *const PR,
    pub(crate) immediates: *const PR,
    pub(crate) fold_weights: *const PR,
    pub(crate) eq_high: *const PR,
    pub(crate) eq_low: *const PR,
    pub(crate) partials: *mut PR,
    pub(crate) c_init_coeff: u32,
    pub(crate) row_tiles: u32,
    pub(crate) eq_sizes: GkrEqSizes,
    pub(crate) reserved1: [u32; 3],
}

const _: () = {
    assert!(MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY == 8_192);
    assert!(MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY == 1_072);
    assert!(MAIN_CONTINUATION_WINDOW_SOURCE_WINDOW_CAPACITY == BWD_SOURCE_WINDOW_SLOTS);
    assert!(MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY == 512);
    assert!(LEAN_CLASS_SHIFT == 13);
    assert!(LEAN_WORDS_PER_TERM == 3);
    assert!(BWD_FOLD_WEIGHT_SLOTS == 11);
    assert!(PR_MAIN_CONTINUATION_BLOCK_THREADS as usize == 32 * PR_MAIN_CONTINUATION_FOLD_LISTS);
    assert!(PR_MAIN_CONTINUATION_TENSOR_CELLS == 27);
    assert!(FIRST_WINDOW_ADDR_SLOT_MAX <= BWD_SOURCE_WINDOW_SLOTS);
    assert!(LATER_WINDOW_ADDR_SLOT_MAX <= BWD_SOURCE_WINDOW_SLOTS);
    assert!(size_of::<MainContinuationSourceRecordPr>() == 4);
    assert!(align_of::<MainContinuationSourceRecordPr>() == 2);
    assert!(offset_of!(MainContinuationSourceRecordPr, src) == 0);
    assert!(offset_of!(MainContinuationSourceRecordPr, publish) == 2);
    assert!(size_of::<MainContinuationWindowLaunchBindingPr>() == 23_936);
    assert!(align_of::<MainContinuationWindowLaunchBindingPr>() == DESCRIPTOR_ALIGNMENT_BYTES);
    assert!(
        size_of::<MainContinuationWindowLaunchBindingPr>()
            + PR_MAIN_CONTINUATION_ARGUMENT_HEADROOM_BYTES
            <= KERNEL_ARGUMENT_CEILING_BYTES
    );
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, program) == 0);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, program_words) == 16_384);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, source_count) == 16_386);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, fold_list_offsets) == 16_388);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, fold_sources) == 16_396);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, source) == 18_540);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, reserved0) == 22_828);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, slot) == 22_832);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, coefficients) == 23_856);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, immediates) == 23_864);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, fold_weights) == 23_872);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, eq_high) == 23_880);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, eq_low) == 23_888);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, partials) == 23_896);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, c_init_coeff) == 23_904);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, row_tiles) == 23_908);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, eq_sizes) == 23_912);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, reserved1) == 23_924);
    assert!(BWD_COEFF_NONE == u32::MAX);
};

#[derive(Clone, Copy, Debug)]
pub(crate) struct MainContinuationScratchPr {
    pub(crate) coefficients: *const PR,
    pub(crate) coefficient_count: usize,
    pub(crate) immediates: *const PR,
    pub(crate) immediate_count: usize,
    pub(crate) fold_weights: *mut PR,
    pub(crate) eq_high: *mut PR,
    pub(crate) eq_low: *mut PR,
    pub(crate) partials: *mut PR,
    pub(crate) partials_capacity: usize,
}

#[derive(Debug)]
pub(crate) enum MainContinuationBindErrorPr {
    Cuda(era_cudart_sys::CudaError),
    Publication(ContinuationPublicationError),
    InvalidGeometry {
        folding_steps: usize,
        start_round: usize,
    },
    Capacity {
        resource: &'static str,
        required: usize,
        capacity: usize,
    },
    NullRuntimePointer {
        resource: &'static str,
    },
    ImmediateCountMismatch {
        program: usize,
        table: usize,
    },
    CoefficientOutOfRange {
        id: usize,
        count: usize,
    },
    ImmediateOutOfRange {
        id: usize,
        count: usize,
    },
    TruncatedProgram {
        word: usize,
    },
    UnresolvedRawSource {
        source: u32,
    },
    RawSourceFieldMismatch {
        source: u32,
        expect_ext: bool,
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

impl From<era_cudart_sys::CudaError> for MainContinuationBindErrorPr {
    fn from(error: era_cudart_sys::CudaError) -> Self {
        Self::Cuda(error)
    }
}

impl From<ContinuationPublicationError> for MainContinuationBindErrorPr {
    fn from(error: ContinuationPublicationError) -> Self {
        Self::Publication(error)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MainContinuationInputKindPr {
    First,
    Later,
}

pub(crate) struct MainContinuationLaunchPr<'input> {
    pub(super) binding: Box<MainContinuationWindowLaunchBindingPr>,
    pub(super) kernel: &'static PrMainContinuationWindowKernelEntry,
    pub(super) published: ContinuationPublishedLevelPr,
    pub(super) row_tiles: usize,
    pub(super) reduced_tensor: *mut PR,
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
) -> Result<([u16; PR_MAIN_CONTINUATION_FOLD_LISTS + 1], Vec<u16>), MainContinuationBindErrorPr> {
    let mut items: Vec<_> = items.into_iter().collect();
    items.sort_unstable_by_key(|item| (core::cmp::Reverse(item.byte_weight), item.source));
    let mut loads = [0usize; PR_MAIN_CONTINUATION_FOLD_LISTS];
    let mut lists: [Vec<u16>; PR_MAIN_CONTINUATION_FOLD_LISTS] =
        std::array::from_fn(|_| Vec::new());
    for item in items {
        let list = (0..PR_MAIN_CONTINUATION_FOLD_LISTS)
            .min_by_key(|list| (loads[*list], *list))
            .expect("the Proth120 continuation executor has three fold lists");
        loads[list] += item.byte_weight;
        lists[list].push(item.source);
    }
    let mut offsets = [0u16; PR_MAIN_CONTINUATION_FOLD_LISTS + 1];
    let mut flattened = Vec::with_capacity(source_count);
    for (list, sources) in lists.into_iter().enumerate() {
        flattened.extend(sources);
        offsets[list + 1] =
            u16::try_from(flattened.len()).map_err(|_| MainContinuationBindErrorPr::Capacity {
                resource: "fold sources",
                required: flattened.len(),
                capacity: u16::MAX as usize,
            })?;
    }
    let mut seen = vec![false; source_count];
    for &source in &flattened {
        let index = usize::from(source);
        if index >= source_count || seen[index] {
            return Err(MainContinuationBindErrorPr::FoldListDuplicate { source });
        }
        seen[index] = true;
    }
    if let Some(source) = seen.iter().position(|present| !present) {
        return Err(MainContinuationBindErrorPr::FoldListMissing {
            source: source as u16,
        });
    }
    Ok((offsets, flattened))
}

struct AddressSlotTable {
    slots: [BwdSourceWindow; BWD_SOURCE_WINDOW_SLOTS],
    len: usize,
}

impl AddressSlotTable {
    fn new() -> Self {
        Self {
            slots: unsafe { core::mem::zeroed() },
            len: 0,
        }
    }

    fn lane(
        &mut self,
        slot: BwdSourceWindow,
        column: usize,
    ) -> Result<u16, MainContinuationBindErrorPr> {
        let index = match self.slots[..self.len].iter().position(|entry| {
            entry.base == slot.base
                && entry.log2_stride == slot.log2_stride
                && entry.origin == slot.origin
                && entry.procedural_kind == slot.procedural_kind
        }) {
            Some(index) => index,
            None => {
                if self.len == self.slots.len() {
                    return Err(MainContinuationBindErrorPr::Capacity {
                        resource: "address slots",
                        required: self.len + 1,
                        capacity: self.slots.len(),
                    });
                }
                self.slots[self.len] = slot;
                self.len += 1;
                self.len - 1
            }
        };
        bwd_source_lane(index, column).ok_or(MainContinuationBindErrorPr::Capacity {
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
    let (Some(first_end), Some(second_end)) = (
        first_start.checked_add(first_bytes),
        second_start.checked_add(second_bytes),
    ) else {
        return true;
    };
    first_start < second_end && second_start < first_end
}

fn checked_pow2(
    exponent: usize,
    folding_steps: usize,
    start_round: usize,
) -> Result<usize, MainContinuationBindErrorPr> {
    u32::try_from(exponent)
        .ok()
        .and_then(|exponent| 1usize.checked_shl(exponent))
        .ok_or(MainContinuationBindErrorPr::InvalidGeometry {
            folding_steps,
            start_round,
        })
}

pub(crate) fn publication_shape_pr(
    program: &MainContinuationWindowProgram,
    folding_steps: usize,
    start_round: usize,
) -> Result<(ContinuationPublishedShape, usize), MainContinuationBindErrorPr> {
    if start_round < PR_MAIN_CONTINUATION_FOLD_COORDINATES
        || !start_round.is_multiple_of(PR_MAIN_CONTINUATION_FOLD_COORDINATES)
        || folding_steps < start_round + PR_MAIN_CONTINUATION_FOLD_COORDINATES
        || start_round > u8::MAX as usize
    {
        return Err(MainContinuationBindErrorPr::InvalidGeometry {
            folding_steps,
            start_round,
        });
    }
    let logical_rows = checked_pow2(
        folding_steps - start_round - PR_MAIN_CONTINUATION_FOLD_COORDINATES,
        folding_steps,
        start_round,
    )?;
    let column_elems =
        logical_rows
            .checked_mul(8)
            .ok_or(MainContinuationBindErrorPr::InvalidGeometry {
                folding_steps,
                start_round,
            })?;
    Ok((
        ContinuationPublishedShape {
            depth: start_round as u8,
            columns: program.sources.len(),
            column_elems,
        },
        logical_rows.div_ceil(PR_MAIN_CONTINUATION_ROWS_PER_TILE),
    ))
}

fn append_canonical_arena_slots(
    table: &mut AddressSlotTable,
    base: *const PR,
    column_elems: usize,
    columns: usize,
) -> Result<Vec<u16>, MainContinuationBindErrorPr> {
    if !column_elems.is_power_of_two() || !(base as usize).is_multiple_of(32) {
        return Err(MainContinuationBindErrorPr::ArenaAlignment {
            address: base as usize,
            column_elems,
        });
    }
    let mut lanes = Vec::with_capacity(columns);
    for source in 0..columns {
        let chunk_elems = (source / SOURCE_WINDOW_COLUMNS)
            .checked_mul(SOURCE_WINDOW_COLUMNS)
            .and_then(|value| value.checked_mul(column_elems))
            .ok_or(MainContinuationBindErrorPr::Capacity {
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
        lanes.push(table.lane(slot, source % SOURCE_WINDOW_COLUMNS)?);
    }
    Ok(lanes)
}

fn raw_input_lanes(
    program: &MainContinuationWindowProgram,
    storage: &GpuGKRStorage<PR, PR>,
    folding_steps: usize,
    destination: &ContinuationPublishedLevelPr,
    table: &mut AddressSlotTable,
) -> Result<(Vec<u16>, Vec<FoldItem>), MainContinuationBindErrorPr> {
    let element_bytes = size_of::<PR>();
    let destination_bytes = destination
        .allocation()
        .len()
        .checked_mul(element_bytes)
        .ok_or(MainContinuationBindErrorPr::InputOutputAlias)?;
    let input_bytes = checked_pow2(folding_steps, folding_steps, 3)?
        .checked_mul(element_bytes)
        .ok_or(MainContinuationBindErrorPr::InputOutputAlias)?;
    let mut lanes = Vec::with_capacity(program.sources.len());
    let mut folds = Vec::with_capacity(program.sources.len());
    for (source_id, source) in program.sources.iter().enumerate() {
        let source_index = source_id as u32;
        if let WindowFamily::VirtualSetup { kind } = source.raw_family {
            if usize::from(kind) >= BWD_COEFF_PROCEDURAL_KINDS {
                return Err(MainContinuationBindErrorPr::UnknownProceduralKind {
                    source: source_index,
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
            MainContinuationBindErrorPr::UnresolvedRawSource {
                source: source_index,
            },
        )?;
        let resolved = resolve_storage_column(storage, read_place_to_gkr_address(&place)).ok_or(
            MainContinuationBindErrorPr::UnresolvedRawSource {
                source: source_index,
            },
        )?;
        let expect_ext = matches!(
            source.raw_family,
            WindowFamily::LayerOutput { ext: true, .. }
                | WindowFamily::CacheOutput { ext: true, .. }
        );
        if resolved.is_e4 != expect_ext {
            return Err(MainContinuationBindErrorPr::RawSourceFieldMismatch {
                source: source_index,
                expect_ext,
            });
        }
        let stride_bytes = resolved.stride_bytes as usize;
        if !stride_bytes.is_multiple_of(element_bytes)
            || !(stride_bytes / element_bytes).is_power_of_two()
        {
            return Err(MainContinuationBindErrorPr::RawSourceStrideMismatch {
                source: source_index,
                stride_bytes: resolved.stride_bytes,
            });
        }
        let pointer = resolved.ptr as usize;
        let matrix = resolved.matrix_base as usize;
        if !pointer.is_multiple_of(32) {
            return Err(MainContinuationBindErrorPr::SourceAlignment {
                source: source_index,
                address: pointer,
            });
        }
        if pointer < matrix || !(pointer - matrix).is_multiple_of(stride_bytes) {
            return Err(MainContinuationBindErrorPr::RawSourceRankMismatch {
                source: source_index,
            });
        }
        let rank = (pointer - matrix) / stride_bytes;
        if pointer_ranges_overlap(
            resolved.ptr,
            input_bytes,
            destination.as_ptr().cast::<u8>(),
            destination_bytes,
        ) {
            return Err(MainContinuationBindErrorPr::InputOutputAlias);
        }
        let slot = BwdSourceWindow {
            base: (matrix + (rank / SOURCE_WINDOW_COLUMNS) * SOURCE_WINDOW_COLUMNS * stride_bytes)
                as *const u8,
            log2_stride: (stride_bytes / element_bytes).trailing_zeros() as u8,
            origin: if expect_ext {
                BWD_COEFF_ORIGIN_READ_EXT
            } else {
                BWD_COEFF_ORIGIN_READ_BASE
            },
            procedural_kind: BWD_COEFF_PROCEDURAL_NONE,
            reserved: 0,
            r0_stride_bytes: 0,
        };
        lanes.push(table.lane(slot, rank % SOURCE_WINDOW_COLUMNS)?);
        folds.push(FoldItem {
            source: source_id as u16,
            byte_weight: 4,
        });
    }
    Ok((lanes, folds))
}

fn prior_input_lanes(
    prior: &ContinuationPublishedLevelPr,
    expected: ContinuationPublishedShape,
    destination: &ContinuationPublishedLevelPr,
    table: &mut AddressSlotTable,
) -> Result<(Vec<u16>, Vec<FoldItem>), MainContinuationBindErrorPr> {
    if prior.shape() != expected {
        return Err(MainContinuationBindErrorPr::PriorShapeMismatch {
            expected,
            actual: prior.shape(),
        });
    }
    let bytes = |level: &ContinuationPublishedLevelPr| {
        level
            .allocation()
            .len()
            .checked_mul(size_of::<PR>())
            .ok_or(MainContinuationBindErrorPr::InputOutputAlias)
    };
    if pointer_ranges_overlap(
        prior.as_ptr().cast::<u8>(),
        bytes(prior)?,
        destination.as_ptr().cast::<u8>(),
        bytes(destination)?,
    ) {
        return Err(MainContinuationBindErrorPr::InputOutputAlias);
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

fn validate_program_ids(
    program: &MainContinuationWindowProgram,
    coefficient_count: usize,
    immediate_count: usize,
) -> Result<(), MainContinuationBindErrorPr> {
    let words = &program.program.words;
    let id = |word: u16| usize::from(word & CONTINUATION_ID_MASK);
    let check_coefficient = |coefficient: usize| {
        if coefficient < coefficient_count {
            Ok(())
        } else {
            Err(MainContinuationBindErrorPr::CoefficientOutOfRange {
                id: coefficient,
                count: coefficient_count,
            })
        }
    };
    if let Some(c_init) = program.c_init {
        check_coefficient(c_init.0 as usize)?;
    }
    let mut pc = 0;
    while pc < words.len() {
        if pc + LEAN_WORDS_PER_TERM > words.len() {
            return Err(MainContinuationBindErrorPr::TruncatedProgram { word: pc });
        }
        let header = words[pc];
        check_coefficient(id(header))?;
        if header >> LEAN_CLASS_SHIFT == LEAN_CONT_GROUP_HEADER_CLASS {
            for _ in 0..words[pc + 1] {
                pc += LEAN_WORDS_PER_TERM;
                if pc + LEAN_WORDS_PER_TERM > words.len() {
                    return Err(MainContinuationBindErrorPr::TruncatedProgram { word: pc });
                }
                let immediate = id(words[pc]);
                if immediate >= PROGRAM_IMMEDIATE_RESERVED
                    && immediate - PROGRAM_IMMEDIATE_RESERVED >= immediate_count
                {
                    return Err(MainContinuationBindErrorPr::ImmediateOutOfRange {
                        id: immediate,
                        count: immediate_count,
                    });
                }
            }
        }
        pc += LEAN_WORDS_PER_TERM;
    }
    Ok(())
}

fn assemble_launch<'input>(
    program: &MainContinuationWindowProgram,
    kernel: &'static PrMainContinuationWindowKernelEntry,
    folding_steps: usize,
    start_round: usize,
    scratch: MainContinuationScratchPr,
    context: &ProverContext,
    input_kind: MainContinuationInputKindPr,
    input_lanes: impl FnOnce(
        &ContinuationPublishedLevelPr,
        &mut AddressSlotTable,
    ) -> Result<(Vec<u16>, Vec<FoldItem>), MainContinuationBindErrorPr>,
) -> Result<MainContinuationLaunchPr<'input>, MainContinuationBindErrorPr> {
    assert_eq!(
        u16::from(kernel.mask),
        program.shape.bits(),
        "Proth120 main continuation kernel mask differs from the program shape"
    );
    for (resource, pointer) in [
        ("coefficients", scratch.coefficients.cast::<u8>()),
        (
            "fold weights",
            scratch.fold_weights.cast_const().cast::<u8>(),
        ),
        ("eq high", scratch.eq_high.cast_const().cast::<u8>()),
        ("eq low", scratch.eq_low.cast_const().cast::<u8>()),
        ("partials", scratch.partials.cast_const().cast::<u8>()),
    ] {
        if pointer.is_null() {
            return Err(MainContinuationBindErrorPr::NullRuntimePointer { resource });
        }
    }
    if scratch.immediate_count != 0 && scratch.immediates.is_null() {
        return Err(MainContinuationBindErrorPr::NullRuntimePointer {
            resource: "immediates",
        });
    }
    if program.immediates.len() != scratch.immediate_count {
        return Err(MainContinuationBindErrorPr::ImmediateCountMismatch {
            program: program.immediates.len(),
            table: scratch.immediate_count,
        });
    }
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
            return Err(MainContinuationBindErrorPr::Capacity {
                resource,
                required,
                capacity,
            });
        }
    }
    validate_program_ids(program, scratch.coefficient_count, scratch.immediate_count)?;
    let (shape, row_tiles) = publication_shape_pr(program, folding_steps, start_round)?;
    let required_partials = PR_MAIN_CONTINUATION_TENSOR_CELLS
        .checked_mul(row_tiles + 1)
        .unwrap_or(usize::MAX);
    if required_partials > scratch.partials_capacity {
        return Err(MainContinuationBindErrorPr::Capacity {
            resource: "partials",
            required: required_partials,
            capacity: scratch.partials_capacity,
        });
    }
    let row_tiles_u32 =
        u32::try_from(row_tiles).map_err(|_| MainContinuationBindErrorPr::Capacity {
            resource: "row tiles",
            required: row_tiles,
            capacity: u32::MAX as usize,
        })?;

    let allocation = context.alloc(
        shape.columns.checked_mul(shape.column_elems).ok_or(
            MainContinuationBindErrorPr::Capacity {
                resource: "publication elements",
                required: usize::MAX,
                capacity: usize::MAX - 1,
            },
        )?,
        AllocationPlacement::Top,
    )?;
    let published = ContinuationPublishedLevelPr::try_new(shape, allocation)?;

    let mut table = AddressSlotTable::new();
    let (read_lanes, folds) = input_lanes(&published, &mut table)?;
    let publish_lanes = append_canonical_arena_slots(
        &mut table,
        published.as_ptr(),
        shape.column_elems,
        shape.columns,
    )?;
    let slot_max = match input_kind {
        MainContinuationInputKindPr::First => FIRST_WINDOW_ADDR_SLOT_MAX,
        MainContinuationInputKindPr::Later => LATER_WINDOW_ADDR_SLOT_MAX,
    };
    if table.len > slot_max {
        return Err(MainContinuationBindErrorPr::Capacity {
            resource: "window address slots",
            required: table.len,
            capacity: slot_max,
        });
    }
    let (fold_list_offsets, fold_sources) = build_fold_lists(folds, shape.columns)?;

    let mut binding: Box<MainContinuationWindowLaunchBindingPr> = unsafe { zeroed_box() };
    binding.program[..program.program.words.len()].copy_from_slice(&program.program.words);
    binding.program_words = program.program.words.len() as u16;
    binding.source_count = shape.columns as u16;
    binding.fold_list_offsets = fold_list_offsets;
    binding.fold_sources[..fold_sources.len()].copy_from_slice(&fold_sources);
    for source in 0..shape.columns {
        binding.source[source] = MainContinuationSourceRecordPr {
            src: read_lanes[source],
            publish: publish_lanes[source],
        };
    }
    binding.slot[..table.len].copy_from_slice(&table.slots[..table.len]);
    binding.coefficients = scratch.coefficients;
    binding.immediates = scratch.immediates;
    binding.fold_weights = scratch.fold_weights.cast_const();
    binding.eq_high = scratch.eq_high.cast_const();
    binding.eq_low = scratch.eq_low.cast_const();
    binding.partials = scratch.partials;
    binding.c_init_coeff = program
        .c_init
        .map_or(BWD_COEFF_NONE, |coefficient| coefficient.0);
    binding.row_tiles = row_tiles_u32;
    binding.eq_sizes =
        make_eq_sizes(folding_steps - start_round - PR_MAIN_CONTINUATION_FOLD_COORDINATES);
    Ok(MainContinuationLaunchPr {
        binding,
        kernel,
        published,
        row_tiles,
        reduced_tensor: scratch
            .partials
            .wrapping_add(PR_MAIN_CONTINUATION_TENSOR_CELLS * row_tiles),
        _input_keepalive: PhantomData,
    })
}

pub(crate) fn bind_first_main_continuation_pr<'input>(
    program: &MainContinuationWindowProgram,
    kernel: &'static PrMainContinuationWindowKernelEntry,
    storage: &'input GpuGKRStorage<PR, PR>,
    folding_steps: usize,
    scratch: MainContinuationScratchPr,
    context: &ProverContext,
) -> Result<MainContinuationLaunchPr<'input>, MainContinuationBindErrorPr> {
    assemble_launch(
        program,
        kernel,
        folding_steps,
        PR_MAIN_CONTINUATION_FOLD_COORDINATES,
        scratch,
        context,
        MainContinuationInputKindPr::First,
        |destination, table| raw_input_lanes(program, storage, folding_steps, destination, table),
    )
}

pub(crate) fn bind_later_main_continuation_pr<'input>(
    program: &MainContinuationWindowProgram,
    kernel: &'static PrMainContinuationWindowKernelEntry,
    prior: &'input ContinuationPublishedLevelPr,
    folding_steps: usize,
    start_round: usize,
    scratch: MainContinuationScratchPr,
    context: &ProverContext,
) -> Result<MainContinuationLaunchPr<'input>, MainContinuationBindErrorPr> {
    let shape = publication_shape_pr(program, folding_steps, start_round)?.0;
    if shape.depth < 2 * PR_MAIN_CONTINUATION_FOLD_COORDINATES as u8 {
        return Err(MainContinuationBindErrorPr::InvalidGeometry {
            folding_steps,
            start_round,
        });
    }
    let expected = ContinuationPublishedShape {
        depth: shape.depth - PR_MAIN_CONTINUATION_FOLD_COORDINATES as u8,
        columns: shape.columns,
        column_elems: shape.column_elems * 8,
    };
    assemble_launch(
        program,
        kernel,
        folding_steps,
        start_round,
        scratch,
        context,
        MainContinuationInputKindPr::Later,
        |destination, table| prior_input_lanes(prior, expected, destination, table),
    )
}

#[cfg(test)]
mod cpu_pr_main_continuation_abi {
    use core::mem::{align_of, offset_of, size_of};

    use super::MainContinuationWindowLaunchBindingPr;

    const CUDA_ABI: &str =
        include_str!("../../../../native/gkr/proth120/backward/fold_prologue_pr.cuh");

    #[test]
    fn cpu_pr_main_continuation_abi_is_exact() {
        assert_eq!(size_of::<MainContinuationWindowLaunchBindingPr>(), 23_936);
        assert_eq!(align_of::<MainContinuationWindowLaunchBindingPr>(), 16);
        for (field, offset) in [
            ("program_words", 16_384),
            ("source_count", 16_386),
            ("fold_list_offsets", 16_388),
            ("fold_sources", 16_396),
            ("source", 18_540),
            ("reserved0", 22_828),
            ("slot", 22_832),
            ("coefficients", 23_856),
            ("immediates", 23_864),
            ("fold_weights", 23_872),
            ("eq_high", 23_880),
            ("eq_low", 23_888),
            ("partials", 23_896),
            ("c_init_coeff", 23_904),
            ("row_tiles", 23_908),
            ("eq_sizes", 23_912),
            ("reserved1", 23_924),
        ] {
            let assertion =
                format!("__builtin_offsetof(bwd_pr_main_cont_desc, {field}) == {offset}");
            assert!(
                CUDA_ABI.contains(&assertion),
                "missing CUDA assertion {assertion}"
            );
        }
        assert!(CUDA_ABI.contains("sizeof(bwd_pr_main_cont_desc) == 23936"));
        assert_eq!(
            offset_of!(MainContinuationWindowLaunchBindingPr, partials),
            23_896
        );
    }
}
