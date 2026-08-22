//! Rust half of the window-3 executor's launch ABI.
//!
//! The matching CUDA definitions and offset assertions live in
//! `native/gkr/backward/window/window_abi.cuh`.

use core::mem::{align_of, offset_of, size_of};

use gpu_core::primitives::field::E4;
use gpu_gkr_compiler::{
    DESCRIPTOR_ALIGNMENT_BYTES, KERNEL_ARGUMENT_CEILING_BYTES, LEAN_MAX_IMMEDIATES,
    MAX_SOURCE_WINDOWS, WINDOW_SECTION_WORDS,
};

use crate::backward::vm::seg_desc::BwdSegAddrSlot;
use crate::backward::GkrEqSizes;

pub(crate) const BWD_WINDOW_ADDR_SLOTS: usize = MAX_SOURCE_WINDOWS;
pub(crate) const BWD_WINDOW_SECTION_WORDS: usize = WINDOW_SECTION_WORDS;
pub(crate) const BWD_WINDOW_MAX_IMMEDIATES: usize = LEAN_MAX_IMMEDIATES;
/// opcode, factor, source_a, source_b.
pub(crate) const BWD_WINDOW_INSTRUCTION_WORDS: usize = 4;
/// Retained-corpus maximum 7,036 words, rounded so the array is a whole number
/// of 16-byte lines.
pub(crate) const BWD_WINDOW_PROGRAM_WORD_CAP: usize = 7_040;

/// The complete by-value launch descriptor of a generated window kernel. Source
/// operands are segmented-VM addressing lanes (`slot:6 << 7 | column:7`) carried
/// directly by the wire, so the window needs no source-slot indirection table.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub(crate) struct WindowLaunchBinding {
    pub slot: [BwdSegAddrSlot; BWD_WINDOW_ADDR_SLOTS],
    pub eq_low: *const E4,
    pub partials: *mut E4,
    pub log_rows: u32,
    pub eq_sizes: GkrEqSizes,
    /// Cumulative instruction endpoints; word 4 carries the shape mask.
    pub sections: [u32; BWD_WINDOW_SECTION_WORDS],
    pub program: [u16; BWD_WINDOW_PROGRAM_WORD_CAP],
    pub immediates: [u32; BWD_WINDOW_MAX_IMMEDIATES],
}

const _: () = {
    assert!(BWD_WINDOW_ADDR_SLOTS == 64);
    assert!(BWD_WINDOW_SECTION_WORDS == 16);
    assert!(BWD_WINDOW_MAX_IMMEDIATES == 512);
    assert!(BWD_WINDOW_PROGRAM_WORD_CAP.is_multiple_of(BWD_WINDOW_INSTRUCTION_WORDS));
    assert!(
        (BWD_WINDOW_PROGRAM_WORD_CAP * size_of::<u16>()).is_multiple_of(DESCRIPTOR_ALIGNMENT_BYTES)
    );

    assert!(size_of::<WindowLaunchBinding>() == 17_248);
    assert!(align_of::<WindowLaunchBinding>() == DESCRIPTOR_ALIGNMENT_BYTES);
    assert!(size_of::<WindowLaunchBinding>() <= KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(offset_of!(WindowLaunchBinding, slot) == 0);
    assert!(offset_of!(WindowLaunchBinding, eq_low) == 1_024);
    assert!(offset_of!(WindowLaunchBinding, partials) == 1_032);
    assert!(offset_of!(WindowLaunchBinding, log_rows) == 1_040);
    assert!(offset_of!(WindowLaunchBinding, eq_sizes) == 1_044);
    assert!(offset_of!(WindowLaunchBinding, sections) == 1_056);
    assert!(offset_of!(WindowLaunchBinding, program) == 1_120);
    assert!(offset_of!(WindowLaunchBinding, immediates) == 15_200);
};
