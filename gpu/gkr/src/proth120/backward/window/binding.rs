use core::mem::{align_of, offset_of, size_of};

use gpu_gkr_compiler::{
    WindowProgram, DESCRIPTOR_ALIGNMENT_BYTES, KERNEL_ARGUMENT_CEILING_BYTES, LEAN_MAX_IMMEDIATES,
    MAX_SOURCE_WINDOWS, WINDOW_SECTION_WORDS,
};

use crate::backward::window::bank::family_read_place;
use crate::backward::window::binding::{
    bind_window_lane, intern_window_slot, rewrite_window_words, window_chunk_address, window_lane,
    window_log_rows, window_partials_len,
};
use crate::backward::window::common::{
    BwdSourceWindow, BWD_COEFF_ORIGIN_PROCEDURAL, BWD_COEFF_ORIGIN_READ_BASE,
    BWD_COEFF_ORIGIN_READ_EXT, BWD_COEFF_PROCEDURAL_KINDS, BWD_COEFF_PROCEDURAL_NONE,
};
use crate::backward::window::zeroed_box;
use crate::backward::{make_eq_sizes, GkrEqSizes, GKR_EQ_GROUP_SIZE, GKR_EQ_HIGH_SLOTS};
use crate::proth120::backward::banks::CoefficientBankViewPr;
use crate::proth120::forward::bind::resolve_storage_column;
use crate::proth120::forward::lower::read_place_to_gkr_address;
use crate::upstream::{FieldKind, PR};
use crate::GpuGKRStorage;

pub(crate) const PR_WINDOW_ADDR_SLOTS: usize = MAX_SOURCE_WINDOWS;
pub(crate) const PR_WINDOW_SECTION_WORDS: usize = WINDOW_SECTION_WORDS;
pub(crate) const PR_WINDOW_INSTRUCTION_WORDS: usize = 4;
pub(crate) const PR_WINDOW_COORDINATES: usize = 3;
pub(crate) const PR_WINDOW_BF_SHAPE_BITS: u16 = 0x8f;
pub(crate) use gpu_gkr_compiler::window::WINDOW_PROGRAM_WORD_CAP as PR_WINDOW_PROGRAM_WORD_CAP;
const PR_WINDOW_MAX_FOLDING_STEPS: usize =
    PR_WINDOW_COORDINATES + GKR_EQ_GROUP_SIZE * (GKR_EQ_HIGH_SLOTS + 1);

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub(crate) struct WindowLaunchBindingPr {
    pub slot: [BwdSourceWindow; PR_WINDOW_ADDR_SLOTS],
    pub eq_low: *const PR,
    pub partials: *mut PR,
    pub log_rows: u32,
    pub eq_sizes: GkrEqSizes,
    pub sections: [u32; PR_WINDOW_SECTION_WORDS],
    pub program: [u16; PR_WINDOW_PROGRAM_WORD_CAP],
    pub eq_high: *const PR,
    pub coefficient_offset: u32,
    pub immediate_offset: u32,
    pub immediate_count: u32,
    pub _pad: u32,
}

const _: () = {
    assert!(PR_WINDOW_ADDR_SLOTS == 64);
    assert!(PR_WINDOW_SECTION_WORDS == 4);
    assert!(PR_WINDOW_PROGRAM_WORD_CAP == 9_216);
    assert!(PR_WINDOW_PROGRAM_WORD_CAP.is_multiple_of(PR_WINDOW_INSTRUCTION_WORDS));
    assert!(size_of::<PR>() == 16);
    assert!(size_of::<WindowLaunchBindingPr>() == 19_536);
    assert!(align_of::<WindowLaunchBindingPr>() == DESCRIPTOR_ALIGNMENT_BYTES);
    assert!(offset_of!(WindowLaunchBindingPr, slot) == 0);
    assert!(offset_of!(WindowLaunchBindingPr, eq_low) == 1_024);
    assert!(offset_of!(WindowLaunchBindingPr, partials) == 1_032);
    assert!(offset_of!(WindowLaunchBindingPr, log_rows) == 1_040);
    assert!(offset_of!(WindowLaunchBindingPr, eq_sizes) == 1_044);
    assert!(offset_of!(WindowLaunchBindingPr, sections) == 1_056);
    assert!(offset_of!(WindowLaunchBindingPr, program) == 1_072);
    assert!(offset_of!(WindowLaunchBindingPr, eq_high) == 19_504);
    assert!(offset_of!(WindowLaunchBindingPr, coefficient_offset) == 19_512);
    assert!(offset_of!(WindowLaunchBindingPr, immediate_offset) == 19_516);
    assert!(offset_of!(WindowLaunchBindingPr, immediate_count) == 19_520);
    assert!(offset_of!(WindowLaunchBindingPr, _pad) == 19_524);
    assert!(size_of::<WindowLaunchBindingPr>() + size_of::<u32>() <= KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(LEAN_MAX_IMMEDIATES == 512);
};

#[derive(Clone, Copy, Debug)]
pub(crate) struct WindowRuntimeScratchPr {
    pub eq_high: *const PR,
    pub eq_low: *const PR,
    pub partials: *mut PR,
    pub partials_capacity: usize,
}

pub(super) struct WindowAddressingPr {
    slots: Vec<BwdSourceWindow>,
    lanes: Vec<Option<u16>>,
}

impl WindowAddressingPr {
    fn intern(&mut self, slot: BwdSourceWindow) -> usize {
        intern_window_slot(&mut self.slots, slot, PR_WINDOW_ADDR_SLOTS).unwrap_or_else(|| {
            panic!(
                "Proth120 binding capacity: window address slots {} exceeds {}",
                PR_WINDOW_ADDR_SLOTS + 1,
                PR_WINDOW_ADDR_SLOTS
            )
        })
    }

    fn bind(&mut self, source: u32, lane: u16) {
        bind_window_lane(&mut self.lanes, source, lane);
    }
}

pub(super) fn intern_window_addressing_pr(
    storage: &GpuGKRStorage<PR, PR>,
    program: &WindowProgram,
) -> WindowAddressingPr {
    let mut addressing = WindowAddressingPr {
        slots: Vec::new(),
        lanes: vec![None; program.source_slots.len()],
    };
    let element = size_of::<PR>() as u32;
    for (index, entry) in program.windows.iter().enumerate() {
        let window = index as u8;
        if let Some(kind) = entry.procedural_kind() {
            assert!(
                usize::from(kind) < BWD_COEFF_PROCEDURAL_KINDS,
                "Proth120 binding UnknownProceduralKind: window={:?}, kind={:?}",
                window,
                kind
            );
            let slot = addressing.intern(BwdSourceWindow {
                base: std::ptr::null(),
                log2_stride: 0,
                origin: BWD_COEFF_ORIGIN_PROCEDURAL,
                procedural_kind: kind,
                reserved: 0,
                r0_stride_bytes: 0,
            });
            let lane = window_lane(slot, 0);
            for column in &entry.columns {
                addressing.bind(column.source, lane);
            }
            continue;
        }
        assert!(
            !entry.columns.is_empty(),
            "Proth120 binding EmptyWindow: window={:?}",
            window
        );
        let expect_e4 = entry.backing_field() == FieldKind::Ext;
        for column in &entry.columns {
            let place = family_read_place(entry.family, column.column)
                .expect("an addressless window is procedural");
            let address = read_place_to_gkr_address(&place);
            let resolved = resolve_storage_column(storage, address).unwrap_or_else(|| {
                panic!(
                    "Proth120 binding UnresolvedWindow: window={:?}, address={:?}",
                    window, address
                )
            });
            assert!(
                resolved.is_e4 == expect_e4,
                "Proth120 binding WindowFieldMismatch: window={:?}, expect_e4={:?}",
                window,
                expect_e4
            );
            assert!(
                (!resolved.ptr.is_null()
                    && (!resolved.matrix_base.is_null()
                        && (resolved.stride_bytes.is_multiple_of(element)
                            && (resolved.stride_bytes / element).is_power_of_two()))),
                "Proth120 binding WindowStrideMismatch: window={:?}, stride_bytes={:?}",
                window,
                resolved.stride_bytes
            );
            let stride = resolved.stride_bytes as usize;
            let pointer = resolved.ptr as usize;
            let matrix = resolved.matrix_base as usize;
            assert!(
                (pointer >= matrix && (pointer - matrix).is_multiple_of(stride)),
                "Proth120 binding UnresolvableRank: window={:?}",
                window
            );
            let (chunk_base, within) = window_chunk_address(matrix, pointer, stride);
            let slot = addressing.intern(BwdSourceWindow {
                base: chunk_base as *const u8,
                log2_stride: (resolved.stride_bytes / element).trailing_zeros() as u8,
                origin: if expect_e4 {
                    BWD_COEFF_ORIGIN_READ_EXT
                } else {
                    BWD_COEFF_ORIGIN_READ_BASE
                },
                procedural_kind: BWD_COEFF_PROCEDURAL_NONE,
                reserved: 0,
                r0_stride_bytes: resolved.stride_bytes,
            });
            addressing.bind(column.source, window_lane(slot, within));
        }
    }
    addressing
}

fn assert_bf_only(program: &WindowProgram) {
    assert_eq!(
        program.shape.bits() & !PR_WINDOW_BF_SHAPE_BITS,
        0,
        "Proth120 R0 program shape {:#x} carries extension-section features",
        program.shape.bits()
    );
    assert!(
        program
            .sections
            .iter()
            .all(|&end| end == program.sections[0]),
        "Proth120 R0 program must be BF-only, sections {:?}",
        program.sections
    );
}

pub(super) fn build_window_binding_pr(
    program: &WindowProgram,
    addressing: &WindowAddressingPr,
    folding_steps: usize,
    scratch: WindowRuntimeScratchPr,
    bank: CoefficientBankViewPr,
) -> Box<WindowLaunchBindingPr> {
    assert_bf_only(program);
    assert!(
        (PR_WINDOW_COORDINATES + 1..=PR_WINDOW_MAX_FOLDING_STEPS).contains(&folding_steps),
        "Proth120 binding UnsupportedFoldingSteps: folding_steps={:?}",
        folding_steps
    );
    assert!(
        !scratch.eq_high.is_null() && !scratch.eq_low.is_null() && !scratch.partials.is_null(),
        "Proth120 R0 scratch pointers must be bound"
    );
    assert_eq!(
        program.immediates.len(),
        bank.immediate_count,
        "Proth120 R0 immediates table length mismatch"
    );
    assert_eq!(
        program.coefficient_plans.len() + 2,
        bank.coefficient_count,
        "Proth120 R0 coefficient bank length mismatch"
    );
    let slots = addressing.slots.as_slice();
    let capacities = [
        ("window address slots", slots.len(), PR_WINDOW_ADDR_SLOTS),
        (
            "window program words",
            program.words.len(),
            PR_WINDOW_PROGRAM_WORD_CAP,
        ),
        (
            "window immediates",
            program.immediates.len(),
            LEAN_MAX_IMMEDIATES,
        ),
    ];
    for (resource, required, capacity) in capacities {
        assert!(
            required <= capacity,
            "Proth120 binding Capacity: resource={:?}, required={:?}, capacity={:?}",
            resource,
            required,
            capacity
        );
    }
    let required_partials = window_partials_len(1usize << folding_steps);
    assert!(
        required_partials <= scratch.partials_capacity,
        "Proth120 binding Capacity: resource={:?}, required={:?}, capacity={:?}",
        "window partials",
        required_partials,
        scratch.partials_capacity
    );
    let mut binding: Box<WindowLaunchBindingPr> = unsafe { zeroed_box() };
    binding.slot[..slots.len()].copy_from_slice(slots);
    binding.eq_low = scratch.eq_low;
    binding.partials = scratch.partials;
    binding.log_rows = window_log_rows(folding_steps);
    binding.eq_sizes = make_eq_sizes(folding_steps - PR_WINDOW_COORDINATES);
    binding.sections = program.sections;
    bind_window_words_pr(program, addressing, &mut binding.program);
    binding.eq_high = scratch.eq_high;
    binding.coefficient_offset = bank.coefficient_offset;
    binding.immediate_offset = bank.immediate_offset;
    binding.immediate_count = bank.immediate_count as u32;
    binding
}

fn bind_window_words_pr(
    program: &WindowProgram,
    addressing: &WindowAddressingPr,
    words: &mut [u16],
) {
    rewrite_window_words(program, &addressing.lanes, words).unwrap_or_else(|(word, source)| {
        panic!("Proth120 binding LaneSourceMissing: word={word:?}, source={source:?}")
    });
}

pub(super) fn bind_r0_window_pr(
    program: &WindowProgram,
    storage: &GpuGKRStorage<PR, PR>,
    folding_steps: usize,
    scratch: WindowRuntimeScratchPr,
    bank: CoefficientBankViewPr,
) -> Box<WindowLaunchBindingPr> {
    let addressing = intern_window_addressing_pr(storage, program);
    build_window_binding_pr(program, &addressing, folding_steps, scratch, bank)
}
