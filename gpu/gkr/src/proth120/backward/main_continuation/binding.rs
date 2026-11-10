use crate::backward::main_continuation::pointer_ranges_overlap;
use core::marker::PhantomData;
use core::mem::{align_of, offset_of, size_of};
use era_cudart::result::CudaResult;

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
use crate::backward::main_continuation::ContinuationPublishedShape;
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
    pub(crate) coefficient_offset: u32,
    pub(crate) immediate_offset: u32,
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
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, coefficient_offset) == 23_856);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, immediate_offset) == 23_860);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, fold_weights) == 23_864);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, eq_high) == 23_872);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, eq_low) == 23_880);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, partials) == 23_888);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, c_init_coeff) == 23_896);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, row_tiles) == 23_900);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, eq_sizes) == 23_904);
    assert!(offset_of!(MainContinuationWindowLaunchBindingPr, reserved1) == 23_916);
    assert!(BWD_COEFF_NONE == u32::MAX);
};

#[derive(Clone, Copy, Debug)]
pub(crate) struct MainContinuationScratchPr {
    pub(crate) coefficient_offset: u32,
    pub(crate) coefficient_count: usize,
    pub(crate) immediate_offset: u32,
    pub(crate) immediate_count: usize,
    pub(crate) fold_weights: *mut PR,
    pub(crate) eq_high: *mut PR,
    pub(crate) eq_low: *mut PR,
    pub(crate) partials: *mut PR,
    pub(crate) partials_capacity: usize,
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
) -> ([u16; PR_MAIN_CONTINUATION_FOLD_LISTS + 1], Vec<u16>) {
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
        offsets[list + 1] = u16::try_from(flattened.len()).unwrap_or_else(|_| {
            panic!(
                "Proth120 continuation capacity (resource={:?}, required={:?}, capacity={:?})",
                "fold sources",
                flattened.len(),
                u16::MAX as usize
            )
        });
    }
    let mut seen = vec![false; source_count];
    for &source in &flattened {
        let index = usize::from(source);
        assert!(
            index < source_count && !seen[index],
            "Proth120 continuation fold list duplicate (source={:?})",
            source
        );
        seen[index] = true;
    }
    let missing = seen.iter().position(|present| !present);
    assert!(
        missing.is_none(),
        "Proth120 continuation fold list is missing source {missing:?}"
    );
    (offsets, flattened)
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

    fn lane(&mut self, slot: BwdSourceWindow, column: usize) -> u16 {
        let index = match self.slots[..self.len].iter().position(|entry| {
            entry.base == slot.base
                && entry.log2_stride == slot.log2_stride
                && entry.origin == slot.origin
                && entry.procedural_kind == slot.procedural_kind
        }) {
            Some(index) => index,
            None => {
                assert!(
                    self.len != self.slots.len(),
                    "Proth120 continuation capacity (resource={:?}, required={:?}, capacity={:?})",
                    "address slots",
                    self.len + 1,
                    self.slots.len()
                );
                self.slots[self.len] = slot;
                self.len += 1;
                self.len - 1
            }
        };
        bwd_source_lane(index, column).unwrap_or_else(|| {
            panic!(
                "Proth120 continuation capacity (resource={:?}, required={:?}, capacity={:?})",
                "address lane column",
                column + 1,
                SOURCE_WINDOW_COLUMNS
            )
        })
    }
}

fn checked_pow2(exponent: usize, folding_steps: usize, start_round: usize) -> usize {
    u32::try_from(exponent)
        .ok()
        .and_then(|exponent| 1usize.checked_shl(exponent))
        .unwrap_or_else(|| {
            panic!(
                "Proth120 continuation invalid geometry (folding_steps={:?}, start_round={:?})",
                folding_steps, start_round
            )
        })
}

pub(crate) fn publication_shape_pr(
    program: &MainContinuationWindowProgram,
    folding_steps: usize,
    start_round: usize,
) -> (ContinuationPublishedShape, usize) {
    assert!(
        start_round >= PR_MAIN_CONTINUATION_FOLD_COORDINATES
            && start_round.is_multiple_of(PR_MAIN_CONTINUATION_FOLD_COORDINATES)
            && folding_steps >= start_round + PR_MAIN_CONTINUATION_FOLD_COORDINATES
            && start_round <= u8::MAX as usize,
        "Proth120 continuation invalid geometry (folding_steps={:?}, start_round={:?})",
        folding_steps,
        start_round
    );
    let logical_rows = checked_pow2(
        folding_steps - start_round - PR_MAIN_CONTINUATION_FOLD_COORDINATES,
        folding_steps,
        start_round,
    );
    let column_elems = logical_rows.checked_mul(8).unwrap_or_else(|| {
        panic!(
            "Proth120 continuation invalid geometry (folding_steps={:?}, start_round={:?})",
            folding_steps, start_round
        )
    });
    (
        ContinuationPublishedShape {
            depth: start_round as u8,
            columns: program.sources.len(),
            column_elems,
        },
        logical_rows.div_ceil(PR_MAIN_CONTINUATION_ROWS_PER_TILE),
    )
}

fn append_canonical_arena_slots(
    table: &mut AddressSlotTable,
    base: *const PR,
    column_elems: usize,
    columns: usize,
) -> Vec<u16> {
    assert!(
        column_elems.is_power_of_two() && (base as usize).is_multiple_of(32),
        "Proth120 continuation arena alignment (address={:?}, column_elems={:?})",
        base as usize,
        column_elems
    );
    let mut lanes = Vec::with_capacity(columns);
    for source in 0..columns {
        let chunk_elems = (source / SOURCE_WINDOW_COLUMNS)
            .checked_mul(SOURCE_WINDOW_COLUMNS)
            .and_then(|value| value.checked_mul(column_elems))
            .unwrap_or_else(|| {
                panic!(
                    "Proth120 continuation capacity (resource={:?}, required={:?}, capacity={:?})",
                    "canonical arena offset",
                    usize::MAX,
                    usize::MAX - 1
                )
            });
        let slot = BwdSourceWindow {
            base: base.wrapping_add(chunk_elems).cast::<u8>(),
            log2_stride: column_elems.trailing_zeros() as u8,
            origin: BWD_COEFF_ORIGIN_READ_EXT,
            procedural_kind: BWD_COEFF_PROCEDURAL_NONE,
            reserved: 0,
            r0_stride_bytes: 0,
        };
        lanes.push(table.lane(slot, source % SOURCE_WINDOW_COLUMNS));
    }
    lanes
}

fn raw_input_lanes(
    program: &MainContinuationWindowProgram,
    storage: &GpuGKRStorage<PR, PR>,
    folding_steps: usize,
    destination: &ContinuationPublishedLevelPr,
    table: &mut AddressSlotTable,
) -> (Vec<u16>, Vec<FoldItem>) {
    let element_bytes = size_of::<PR>();
    let destination_bytes = destination
        .allocation()
        .len()
        .checked_mul(element_bytes)
        .unwrap_or_else(|| panic!("Proth120 continuation input output alias"));
    let input_bytes = checked_pow2(folding_steps, folding_steps, 3)
        .checked_mul(element_bytes)
        .unwrap_or_else(|| panic!("Proth120 continuation input output alias"));
    let mut lanes = Vec::with_capacity(program.sources.len());
    let mut folds = Vec::with_capacity(program.sources.len());
    for (source_id, source) in program.sources.iter().enumerate() {
        let source_index = source_id as u32;
        if let WindowFamily::VirtualSetup { kind } = source.raw_family {
            assert!(
                usize::from(kind) < BWD_COEFF_PROCEDURAL_KINDS,
                "Proth120 continuation unknown procedural kind (source={:?}, kind={:?})",
                source_index,
                kind
            );
            let slot = BwdSourceWindow {
                base: core::ptr::null(),
                log2_stride: 0,
                origin: BWD_COEFF_ORIGIN_PROCEDURAL,
                procedural_kind: kind,
                reserved: 0,
                r0_stride_bytes: 0,
            };
            lanes.push(table.lane(slot, 0));
            folds.push(FoldItem {
                source: source_id as u16,
                byte_weight: 1,
            });
            continue;
        }
        let place = family_read_place(source.raw_family, source.raw_column).unwrap_or_else(|| {
            panic!(
                "Proth120 continuation unresolved raw source (source={:?})",
                source_index
            )
        });
        let resolved = resolve_storage_column(storage, read_place_to_gkr_address(&place))
            .unwrap_or_else(|| {
                panic!(
                    "Proth120 continuation unresolved raw source (source={:?})",
                    source_index
                )
            });
        let expect_ext = matches!(
            source.raw_family,
            WindowFamily::LayerOutput { ext: true, .. }
                | WindowFamily::CacheOutput { ext: true, .. }
        );
        assert!(
            resolved.is_e4 == expect_ext,
            "Proth120 continuation raw source field mismatch (source={:?}, expect_ext={:?})",
            source_index,
            expect_ext
        );
        let stride_bytes = resolved.stride_bytes as usize;
        assert!(
            stride_bytes.is_multiple_of(element_bytes)
                && (stride_bytes / element_bytes).is_power_of_two(),
            "Proth120 continuation raw source stride mismatch (source={:?}, stride_bytes={:?})",
            source_index,
            resolved.stride_bytes
        );
        let pointer = resolved.ptr as usize;
        let matrix = resolved.matrix_base as usize;
        assert!(
            pointer.is_multiple_of(32),
            "Proth120 continuation source alignment (source={:?}, address={:?})",
            source_index,
            pointer
        );
        assert!(
            pointer >= matrix && (pointer - matrix).is_multiple_of(stride_bytes),
            "Proth120 continuation raw source rank mismatch (source={:?})",
            source_index
        );
        let rank = (pointer - matrix) / stride_bytes;
        assert!(
            !pointer_ranges_overlap(
                resolved.ptr,
                input_bytes,
                destination.as_ptr().cast::<u8>(),
                destination_bytes,
            ),
            "Proth120 continuation input output alias"
        );
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
        lanes.push(table.lane(slot, rank % SOURCE_WINDOW_COLUMNS));
        folds.push(FoldItem {
            source: source_id as u16,
            byte_weight: 4,
        });
    }
    (lanes, folds)
}

fn prior_input_lanes(
    prior: &ContinuationPublishedLevelPr,
    expected: ContinuationPublishedShape,
    destination: &ContinuationPublishedLevelPr,
    table: &mut AddressSlotTable,
) -> (Vec<u16>, Vec<FoldItem>) {
    assert!(
        prior.shape() == expected,
        "Proth120 continuation prior shape mismatch (expected={:?}, actual={:?})",
        expected,
        prior.shape()
    );
    let bytes = |level: &ContinuationPublishedLevelPr| {
        level
            .allocation()
            .len()
            .checked_mul(size_of::<PR>())
            .unwrap_or_else(|| panic!("Proth120 continuation input output alias"))
    };
    assert!(
        !pointer_ranges_overlap(
            prior.as_ptr().cast::<u8>(),
            bytes(prior),
            destination.as_ptr().cast::<u8>(),
            bytes(destination),
        ),
        "Proth120 continuation input output alias"
    );
    let lanes = append_canonical_arena_slots(
        table,
        prior.as_ptr(),
        prior.shape().column_elems,
        prior.shape().columns,
    );
    let folds = (0..expected.columns)
        .map(|source| FoldItem {
            source: source as u16,
            byte_weight: 4,
        })
        .collect();
    (lanes, folds)
}

fn validate_program_ids(
    program: &MainContinuationWindowProgram,
    coefficient_count: usize,
    immediate_count: usize,
) {
    let words = &program.program.words;
    let id = |word: u16| usize::from(word & CONTINUATION_ID_MASK);
    let check_coefficient = |coefficient: usize| {
        assert!(
            coefficient < coefficient_count,
            "Proth120 coefficient {coefficient} exceeds {coefficient_count}"
        );
    };
    if let Some(c_init) = program.c_init {
        check_coefficient(c_init.0 as usize);
    }
    let mut pc = 0;
    while pc < words.len() {
        assert!(
            pc + LEAN_WORDS_PER_TERM <= words.len(),
            "Proth120 continuation truncated program (word={:?})",
            pc
        );
        let header = words[pc];
        check_coefficient(id(header));
        if header >> LEAN_CLASS_SHIFT == LEAN_CONT_GROUP_HEADER_CLASS {
            for _ in 0..words[pc + 1] {
                pc += LEAN_WORDS_PER_TERM;
                assert!(
                    pc + LEAN_WORDS_PER_TERM <= words.len(),
                    "Proth120 continuation truncated program (word={:?})",
                    pc
                );
                let immediate = id(words[pc]);
                assert!(
                    immediate < PROGRAM_IMMEDIATE_RESERVED
                        || immediate - PROGRAM_IMMEDIATE_RESERVED < immediate_count,
                    "Proth120 continuation immediate out of range (id={:?}, count={:?})",
                    immediate,
                    immediate_count
                );
            }
        }
        pc += LEAN_WORDS_PER_TERM;
    }
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
    ) -> (Vec<u16>, Vec<FoldItem>),
) -> CudaResult<MainContinuationLaunchPr<'input>> {
    assert_eq!(
        u16::from(kernel.mask),
        program.shape.bits(),
        "Proth120 main continuation kernel mask differs from the program shape"
    );
    for (resource, pointer) in [
        (
            "fold weights",
            scratch.fold_weights.cast_const().cast::<u8>(),
        ),
        ("eq high", scratch.eq_high.cast_const().cast::<u8>()),
        ("eq low", scratch.eq_low.cast_const().cast::<u8>()),
        ("partials", scratch.partials.cast_const().cast::<u8>()),
    ] {
        assert!(
            !pointer.is_null(),
            "Proth120 continuation null runtime pointer (resource={:?})",
            resource
        );
    }
    assert!(
        program.immediates.len() == scratch.immediate_count,
        "Proth120 continuation immediate count mismatch (program={:?}, table={:?})",
        program.immediates.len(),
        scratch.immediate_count
    );
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
        assert!(
            required <= capacity,
            "Proth120 continuation capacity (resource={:?}, required={:?}, capacity={:?})",
            resource,
            required,
            capacity
        );
    }
    validate_program_ids(program, scratch.coefficient_count, scratch.immediate_count);
    let (shape, row_tiles) = publication_shape_pr(program, folding_steps, start_round);
    let required_partials = PR_MAIN_CONTINUATION_TENSOR_CELLS.saturating_mul(row_tiles + 1);
    assert!(
        required_partials <= scratch.partials_capacity,
        "Proth120 continuation capacity (resource={:?}, required={:?}, capacity={:?})",
        "partials",
        required_partials,
        scratch.partials_capacity
    );
    let row_tiles_u32 = u32::try_from(row_tiles).unwrap_or_else(|_| {
        panic!(
            "Proth120 continuation capacity (resource={:?}, required={:?}, capacity={:?})",
            "row tiles",
            row_tiles,
            u32::MAX as usize
        )
    });

    let allocation = context.alloc(
        shape
            .columns
            .checked_mul(shape.column_elems)
            .unwrap_or_else(|| {
                panic!(
                    "Proth120 continuation capacity (resource={:?}, required={:?}, capacity={:?})",
                    "publication elements",
                    usize::MAX,
                    usize::MAX - 1
                )
            }),
        AllocationPlacement::Top,
    )?;
    let published = ContinuationPublishedLevelPr::new(shape, allocation);

    let mut table = AddressSlotTable::new();
    let (read_lanes, folds) = input_lanes(&published, &mut table);
    let publish_lanes = append_canonical_arena_slots(
        &mut table,
        published.as_ptr(),
        shape.column_elems,
        shape.columns,
    );
    let slot_max = match input_kind {
        MainContinuationInputKindPr::First => FIRST_WINDOW_ADDR_SLOT_MAX,
        MainContinuationInputKindPr::Later => LATER_WINDOW_ADDR_SLOT_MAX,
    };
    assert!(
        table.len <= slot_max,
        "Proth120 continuation capacity (resource={:?}, required={:?}, capacity={:?})",
        "window address slots",
        table.len,
        slot_max
    );
    let (fold_list_offsets, fold_sources) = build_fold_lists(folds, shape.columns);

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
    binding.coefficient_offset = scratch.coefficient_offset;
    binding.immediate_offset = scratch.immediate_offset;
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
) -> CudaResult<MainContinuationLaunchPr<'input>> {
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
) -> CudaResult<MainContinuationLaunchPr<'input>> {
    let shape = publication_shape_pr(program, folding_steps, start_round).0;
    assert!(
        shape.depth >= 2 * PR_MAIN_CONTINUATION_FOLD_COORDINATES as u8,
        "Proth120 continuation invalid geometry (folding_steps={:?}, start_round={:?})",
        folding_steps,
        start_round
    );
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
            ("coefficient_offset", 23_856),
            ("immediate_offset", 23_860),
            ("fold_weights", 23_864),
            ("eq_high", 23_872),
            ("eq_low", 23_880),
            ("partials", 23_888),
            ("c_init_coeff", 23_896),
            ("row_tiles", 23_900),
            ("eq_sizes", 23_904),
            ("reserved1", 23_916),
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
            23_888
        );
    }
}
