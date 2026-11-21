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
        window::{binding::*, common::BwdSourceWindow, zeroed_box},
        GkrEqSizes,
    },
    upstream::PrimeField,
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

pub(super) fn intern_window_addressing<E: Copy>(
    storage: &GpuGKRStorage<BF, E>,
    program: &WindowProgram,
) -> Result<WindowAddressing, WindowBindError> {
    crate::backward::window::binding::intern_window_addressing::<BF, E4>(program, |address| {
        resolve_storage_column(storage, address)
    })
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
