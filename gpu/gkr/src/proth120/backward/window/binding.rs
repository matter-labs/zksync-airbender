use core::mem::{align_of, offset_of, size_of};

use gpu_gkr_compiler::window::partition::R0PartitionPlan;
use gpu_gkr_compiler::{
    WindowProgram, DESCRIPTOR_ALIGNMENT_BYTES, KERNEL_ARGUMENT_CEILING_BYTES, LEAN_MAX_IMMEDIATES,
    MAX_SOURCE_WINDOWS, SOURCE_WINDOW_COLUMNS, WINDOW_SECTION_WORDS,
};

use crate::backward::window::bank::family_read_place;
use crate::backward::window::binding::{window_log_rows, window_partials_len, WindowBindError};
use crate::backward::window::common::{
    BwdSourceWindow, BWD_COEFF_ORIGIN_PROCEDURAL, BWD_COEFF_ORIGIN_READ_BASE,
    BWD_COEFF_ORIGIN_READ_EXT, BWD_COEFF_PROCEDURAL_KINDS, BWD_COEFF_PROCEDURAL_NONE,
    BWD_SOURCE_LANE_COLUMN_BITS,
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
pub(crate) const PR_WINDOW_MAX_PARTS: usize = 16;
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
    pub coefficients: *const PR,
    pub immediates: *const PR,
    pub immediate_count: u32,
    pub _pad: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(crate) struct PartitionBoundsPr {
    pub parts: u32,
    pub ends: [[u32; PR_WINDOW_SECTION_WORDS]; PR_WINDOW_MAX_PARTS],
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
    assert!(offset_of!(WindowLaunchBindingPr, coefficients) == 19_512);
    assert!(offset_of!(WindowLaunchBindingPr, immediates) == 19_520);
    assert!(offset_of!(WindowLaunchBindingPr, immediate_count) == 19_528);
    assert!(offset_of!(WindowLaunchBindingPr, _pad) == 19_532);
    assert!(size_of::<PartitionBoundsPr>() == 260);
    assert!(align_of::<PartitionBoundsPr>() == 4);
    assert!(offset_of!(PartitionBoundsPr, ends) == 4);
    assert!(
        size_of::<WindowLaunchBindingPr>() + size_of::<u32>() + size_of::<PartitionBoundsPr>()
            <= KERNEL_ARGUMENT_CEILING_BYTES
    );
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
    fn intern(&mut self, slot: BwdSourceWindow) -> Result<usize, WindowBindError> {
        if let Some(index) = self.slots.iter().position(|entry| {
            entry.base == slot.base
                && entry.log2_stride == slot.log2_stride
                && entry.r0_stride_bytes == slot.r0_stride_bytes
                && entry.origin == slot.origin
                && entry.procedural_kind == slot.procedural_kind
        }) {
            return Ok(index);
        }
        if self.slots.len() == PR_WINDOW_ADDR_SLOTS {
            return Err(WindowBindError::Capacity {
                resource: "window address slots",
                required: PR_WINDOW_ADDR_SLOTS + 1,
                capacity: PR_WINDOW_ADDR_SLOTS,
            });
        }
        self.slots.push(slot);
        Ok(self.slots.len() - 1)
    }

    fn bind(&mut self, source: u32, lane: u16) {
        let source = source as usize;
        if source >= self.lanes.len() {
            self.lanes.resize(source + 1, None);
        }
        self.lanes[source] = Some(lane);
    }
}

fn window_lane(slot: usize, column: usize) -> u16 {
    ((slot << BWD_SOURCE_LANE_COLUMN_BITS) | column) as u16
}

fn window_chunk_address(matrix: usize, pointer: usize, stride: usize) -> (usize, usize) {
    let rank = (pointer - matrix) / stride;
    let chunk = rank / SOURCE_WINDOW_COLUMNS;
    (
        matrix + chunk * SOURCE_WINDOW_COLUMNS * stride,
        rank % SOURCE_WINDOW_COLUMNS,
    )
}

pub(super) fn intern_window_addressing_pr(
    storage: &GpuGKRStorage<PR, PR>,
    program: &WindowProgram,
) -> Result<WindowAddressingPr, WindowBindError> {
    let mut addressing = WindowAddressingPr {
        slots: Vec::new(),
        lanes: vec![None; program.source_slots.len()],
    };
    let element = size_of::<PR>() as u32;
    for (index, entry) in program.windows.iter().enumerate() {
        let window = index as u8;
        if let Some(kind) = entry.procedural_kind() {
            if usize::from(kind) >= BWD_COEFF_PROCEDURAL_KINDS {
                return Err(WindowBindError::UnknownProceduralKind { window, kind });
            }
            let slot = addressing.intern(BwdSourceWindow {
                base: std::ptr::null(),
                log2_stride: 0,
                origin: BWD_COEFF_ORIGIN_PROCEDURAL,
                procedural_kind: kind,
                reserved: 0,
                r0_stride_bytes: 0,
            })?;
            let lane = window_lane(slot, 0);
            for column in &entry.columns {
                addressing.bind(column.source, lane);
            }
            continue;
        }
        if entry.columns.is_empty() {
            return Err(WindowBindError::EmptyWindow { window });
        }
        let expect_e4 = entry.backing_field() == FieldKind::Ext;
        for column in &entry.columns {
            let place = family_read_place(entry.family, column.column)
                .expect("an addressless window is procedural");
            let address = read_place_to_gkr_address(&place);
            let resolved = resolve_storage_column(storage, address)
                .ok_or(WindowBindError::UnresolvedWindow { window, address })?;
            if resolved.is_e4 != expect_e4 {
                return Err(WindowBindError::WindowFieldMismatch { window, expect_e4 });
            }
            if resolved.ptr.is_null()
                || resolved.matrix_base.is_null()
                || !resolved.stride_bytes.is_multiple_of(element)
                || !(resolved.stride_bytes / element).is_power_of_two()
            {
                return Err(WindowBindError::WindowStrideMismatch {
                    window,
                    stride_bytes: resolved.stride_bytes,
                });
            }
            let stride = resolved.stride_bytes as usize;
            let pointer = resolved.ptr as usize;
            let matrix = resolved.matrix_base as usize;
            if pointer < matrix || !(pointer - matrix).is_multiple_of(stride) {
                return Err(WindowBindError::UnresolvableRank { window });
            }
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
            })?;
            addressing.bind(column.source, window_lane(slot, within));
        }
    }
    Ok(addressing)
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
) -> Result<Box<WindowLaunchBindingPr>, WindowBindError> {
    assert_bf_only(program);
    if !(PR_WINDOW_COORDINATES + 1..=PR_WINDOW_MAX_FOLDING_STEPS).contains(&folding_steps) {
        return Err(WindowBindError::UnsupportedFoldingSteps { folding_steps });
    }
    assert!(
        !scratch.eq_high.is_null() && !scratch.eq_low.is_null() && !scratch.partials.is_null(),
        "Proth120 R0 scratch pointers must be bound"
    );
    assert!(
        !bank.coefficients.is_null(),
        "Proth120 R0 coefficient bank must be bound"
    );
    assert_eq!(
        program.immediates.len(),
        bank.immediate_count,
        "Proth120 R0 immediates table length mismatch"
    );
    assert!(
        bank.immediate_count == 0 || !bank.immediates.is_null(),
        "Proth120 R0 immediates table must be bound"
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
        if required > capacity {
            return Err(WindowBindError::Capacity {
                resource,
                required,
                capacity,
            });
        }
    }
    let required_partials = window_partials_len(1usize << folding_steps);
    if required_partials > scratch.partials_capacity {
        return Err(WindowBindError::Capacity {
            resource: "window partials",
            required: required_partials,
            capacity: scratch.partials_capacity,
        });
    }
    let mut binding: Box<WindowLaunchBindingPr> = unsafe { zeroed_box() };
    binding.slot[..slots.len()].copy_from_slice(slots);
    binding.eq_low = scratch.eq_low;
    binding.partials = scratch.partials;
    binding.log_rows = window_log_rows(folding_steps);
    binding.eq_sizes = make_eq_sizes(folding_steps - PR_WINDOW_COORDINATES);
    binding.sections = program.sections;
    bind_window_words_pr(program, addressing, &mut binding.program)?;
    binding.eq_high = scratch.eq_high;
    binding.coefficients = bank.coefficients;
    binding.immediates = bank.immediates;
    binding.immediate_count = bank.immediate_count as u32;
    Ok(binding)
}

pub(super) fn bind_window_words_pr(
    program: &WindowProgram,
    addressing: &WindowAddressingPr,
    words: &mut [u16],
) -> Result<(), WindowBindError> {
    words[..program.words.len()].copy_from_slice(&program.words);
    for lane in &program.source_lanes {
        let word = lane.word as usize;
        let runtime = addressing
            .lanes
            .get(usize::from(lane.source))
            .copied()
            .flatten()
            .ok_or(WindowBindError::LaneSourceMissing {
                word: lane.word,
                source: lane.source,
            })?;
        *words
            .get_mut(word)
            .ok_or(WindowBindError::LaneSourceMissing {
                word: lane.word,
                source: lane.source,
            })? = runtime;
    }
    Ok(())
}

pub(super) fn bind_r0_window_pr(
    program: &WindowProgram,
    plan: Option<&R0PartitionPlan>,
    storage: &GpuGKRStorage<PR, PR>,
    folding_steps: usize,
    scratch: WindowRuntimeScratchPr,
    bank: CoefficientBankViewPr,
) -> Result<(Box<WindowLaunchBindingPr>, Option<PartitionBoundsPr>), WindowBindError> {
    let addressing = intern_window_addressing_pr(storage, program)?;
    let mut combined = build_window_binding_pr(program, &addressing, folding_steps, scratch, bank)?;
    let Some(plan) = plan.filter(|plan| plan.parts.len() > 1) else {
        return Ok((combined, None));
    };
    assert!(
        plan.parts.len() <= PR_WINDOW_MAX_PARTS,
        "Proth120 R0 partition plan exceeds {PR_WINDOW_MAX_PARTS} parts"
    );
    combined.program.fill(0);
    let mut bounds = PartitionBoundsPr {
        parts: plan.parts.len() as u32,
        ..Default::default()
    };
    let mut base = 0usize;
    for (index, part) in plan.parts.iter().enumerate() {
        assert_bf_only(part);
        let count = part.sections[PR_WINDOW_SECTION_WORDS - 1] as usize;
        bind_window_words_pr(
            part,
            &addressing,
            &mut combined.program
                [PR_WINDOW_INSTRUCTION_WORDS * base..PR_WINDOW_INSTRUCTION_WORDS * (base + count)],
        )?;
        for section in 0..PR_WINDOW_SECTION_WORDS {
            bounds.ends[index][section] = base as u32 + part.sections[section];
        }
        base += count;
    }
    assert_eq!(
        base,
        program.sections[PR_WINDOW_SECTION_WORDS - 1] as usize,
        "Proth120 R0 partition parts must cover the program"
    );
    Ok((combined, Some(bounds)))
}
