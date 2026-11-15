//! Rust half of the window-3 executor's launch ABI, plus the runtime binder
//! that turns a static [`WindowProgram`] into a launch-ready descriptor.
//!
//! The matching CUDA definitions and offset assertions live in
//! `native/gkr/backward/window/window_abi.cuh`.
use core::mem::{align_of, offset_of, size_of};

use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::{WindowProgram, DESCRIPTOR_ALIGNMENT_BYTES, KERNEL_ARGUMENT_CEILING_BYTES};

use crate::{
    baby_bear::forward::vm::production_bind::resolve_storage_column,
    backward::{
        make_eq_sizes,
        window::{
            bank::family_read_place,
            binding::*,
            common::{
                BwdSourceWindow, BWD_COEFF_ORIGIN_PROCEDURAL, BWD_COEFF_ORIGIN_READ_BASE,
                BWD_COEFF_ORIGIN_READ_EXT, BWD_COEFF_PROCEDURAL_KINDS, BWD_COEFF_PROCEDURAL_NONE,
            },
            zeroed_box,
        },
        GkrEqSizes,
    },
    forward::vm::lower_common::read_place_to_gkr_address,
    upstream::{FieldKind, PrimeField},
    GpuGKRStorage,
};

/// The complete by-value launch descriptor of a generated window kernel. Source
/// operands are source-window lanes (`slot:6 << 7 | column:7`) carried
/// directly by the wire — the binder rewrites the lowered lanes to the ones
/// storage implies, so the kernel needs no source-slot indirection table.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub(crate) struct WindowLaunchBinding {
    pub slot: [BwdSourceWindow; BWD_WINDOW_ADDR_SLOTS],
    pub eq_low: *const E4,
    pub partials: *mut E4,
    pub log_rows: u32,
    pub eq_sizes: GkrEqSizes,
    /// Cumulative instruction endpoints.
    pub sections: [u32; BWD_WINDOW_SECTION_WORDS],
    pub program: [u16; BWD_WINDOW_PROGRAM_WORD_CAP],
    pub immediates: [u32; BWD_WINDOW_MAX_IMMEDIATES],
}

const _: () = {
    assert!(BWD_WINDOW_ADDR_SLOTS == 64);
    assert!(BWD_WINDOW_SECTION_WORDS == 4);
    assert!(BWD_WINDOW_MAX_IMMEDIATES == 512);
    assert!(BWD_WINDOW_PROGRAM_WORD_CAP.is_multiple_of(BWD_WINDOW_INSTRUCTION_WORDS));
    assert!(
        (BWD_WINDOW_PROGRAM_WORD_CAP * size_of::<u16>()).is_multiple_of(DESCRIPTOR_ALIGNMENT_BYTES)
    );

    assert!(size_of::<WindowLaunchBinding>() == 21_552);
    assert!(align_of::<WindowLaunchBinding>() == DESCRIPTOR_ALIGNMENT_BYTES);
    assert!(size_of::<WindowLaunchBinding>() + size_of::<u32>() <= KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(offset_of!(WindowLaunchBinding, slot) == 0);
    assert!(offset_of!(WindowLaunchBinding, eq_low) == 1_024);
    assert!(offset_of!(WindowLaunchBinding, partials) == 1_032);
    assert!(offset_of!(WindowLaunchBinding, log_rows) == 1_040);
    assert!(offset_of!(WindowLaunchBinding, eq_sizes) == 1_044);
    assert!(offset_of!(WindowLaunchBinding, sections) == 1_056);
    assert!(offset_of!(WindowLaunchBinding, program) == 1_072);
    assert!(offset_of!(WindowLaunchBinding, immediates) == 19_504);
};

/// The layer-scoped runtime addresses a window launch binds.
#[derive(Clone, Copy, Debug)]
pub(crate) struct WindowRuntimeScratch {
    /// Production factored-eq low table; the high tables stay in `ab_gkr_eq_high`.
    pub eq_low: *const E4,
    /// The layer's shared partials buffer, sized by [`window_partials_len`].
    pub partials: *mut E4,
    pub partials_capacity: usize,
}

/// The window's runtime addressing: one slot per storage chunk actually read,
/// and the lane each source slot resolved to.
pub(super) struct WindowAddressing {
    pub(super) slots: Vec<BwdSourceWindow>,
    /// Indexed by source slot id; `None` for a source no window binds.
    pub(super) lanes: Vec<Option<u16>>,
}

impl WindowAddressing {
    fn intern(&mut self, slot: BwdSourceWindow) -> Result<usize, WindowBindError> {
        intern_window_slot(&mut self.slots, slot, BWD_WINDOW_ADDR_SLOTS).ok_or(
            WindowBindError::Capacity {
                resource: "window address slots",
                required: BWD_WINDOW_ADDR_SLOTS + 1,
                capacity: BWD_WINDOW_ADDR_SLOTS,
            },
        )
    }

    fn bind(&mut self, source: u32, lane: u16) {
        bind_window_lane(&mut self.lanes, source, lane);
    }
}

/// Re-address every column the lowered windows reference, against production
/// storage.
///
/// The lowered wire carries the ARTIFACT's `(window, relative column)` lanes,
/// but a source's address is a fact about storage: a layer's columns are
/// allocated per storage class, so one artifact window's columns can sit in
/// different matrices. So each column is interned into the slot its own pointer
/// implies — chunk base plus rank within the chunk — and the binder rewrites
/// the wire's lane words from the result.
pub(super) fn intern_window_addressing<E: Copy>(
    storage: &GpuGKRStorage<BF, E>,
    program: &WindowProgram,
) -> Result<WindowAddressing, WindowBindError> {
    let mut addressing = WindowAddressing {
        slots: Vec::new(),
        lanes: vec![None; program.source_slots.len()],
    };
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
        let element = if expect_e4 {
            size_of::<E4>()
        } else {
            size_of::<BF>()
        } as u32;
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

/// Assemble the descriptor from the static program, the resolved address slots,
/// and the layer's runtime scratch.
///
/// The static program carries no trace shape, so `log_rows` and the eq schedule
/// are computed here: a window consumes three coordinates per launch, leaving
/// `folding_steps - 3` for its row axis.
pub(super) fn build_window_binding(
    program: &WindowProgram,
    addressing: &WindowAddressing,
    folding_steps: usize,
    scratch: WindowRuntimeScratch,
) -> Result<Box<WindowLaunchBinding>, WindowBindError> {
    let slots = addressing.slots.as_slice();
    if !(BWD_WINDOW_COORDINATES + 1..=BWD_WINDOW_MAX_FOLDING_STEPS).contains(&folding_steps) {
        return Err(WindowBindError::UnsupportedFoldingSteps { folding_steps });
    }
    let capacities = [
        ("window address slots", slots.len(), BWD_WINDOW_ADDR_SLOTS),
        (
            "window program words",
            program.words.len(),
            BWD_WINDOW_PROGRAM_WORD_CAP,
        ),
        (
            "window immediates",
            program.immediates.len(),
            BWD_WINDOW_MAX_IMMEDIATES,
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

    // SAFETY: every field of the descriptor is valid all-zero — the two pointers
    // as null, the rest as zeroed integers.
    let mut binding: Box<WindowLaunchBinding> = unsafe { zeroed_box() };
    binding.slot[..slots.len()].copy_from_slice(slots);
    binding.eq_low = scratch.eq_low;
    binding.partials = scratch.partials;
    binding.log_rows = window_log_rows(folding_steps);
    binding.eq_sizes = make_eq_sizes(folding_steps - BWD_WINDOW_COORDINATES);
    binding.sections = program.sections;
    bind_window_words(program, addressing, &mut binding.program)?;
    for (raw, &canonical) in binding.immediates[..program.immediates.len()]
        .iter_mut()
        .zip(&program.immediates)
    {
        *raw = crate::baby_bear::backward::babybear_from_canonical(canonical)
            .as_u32_raw_repr_reduced();
    }
    Ok(binding)
}

pub(super) fn bind_window_words(
    program: &WindowProgram,
    addressing: &WindowAddressing,
    words: &mut [u16],
) -> Result<(), WindowBindError> {
    rewrite_window_words(program, &addressing.lanes, words)
        .map_err(|(word, source)| WindowBindError::LaneSourceMissing { word, source })
}
