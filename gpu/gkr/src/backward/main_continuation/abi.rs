//! Rust mirror of the main continuation window launch descriptor.
//!
//! The matching CUDA layout and its independent offset assertions live in
//! `native/gkr/backward/main_continuation_window/main_continuation_window_abi.cuh`.

use core::mem::{align_of, offset_of, size_of};

use gpu_core::primitives::field::E4;
use gpu_gkr_compiler::{
    DESCRIPTOR_ALIGNMENT_BYTES, KERNEL_ARGUMENT_CEILING_BYTES,
    MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY, MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY,
    MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY, MAIN_CONTINUATION_WINDOW_SOURCE_WINDOW_CAPACITY,
    SOURCE_NONE,
};

use crate::backward::vm::seg_desc::{BwdSegAddrSlot, BWD_SEG_ADDR_NONE, BWD_SEG_C_INIT_NONE};
use crate::backward::GkrEqSizes;

pub(crate) const MAIN_CONTINUATION_WINDOW_WARPS: usize = 9;
pub(crate) const MAIN_CONTINUATION_WINDOW_BLOCK_WARPS: usize = 3;
pub(crate) const MAIN_CONTINUATION_WINDOW_SELECTOR_BLOCKS: usize = 3;
pub(crate) const MAIN_CONTINUATION_WINDOW_THREADS: u32 =
    32 * MAIN_CONTINUATION_WINDOW_BLOCK_WARPS as u32;
pub(crate) const MAIN_CONTINUATION_WINDOW_PUBLICATION_THREADS: u32 =
    32 * MAIN_CONTINUATION_WINDOW_BLOCK_WARPS as u32;
pub(crate) const MAIN_CONTINUATION_WINDOW_PUBLICATION_LANES_PER_ROW: usize = 4;
pub(crate) const MAIN_CONTINUATION_WINDOW_PUBLICATION_ROWS_PER_BLOCK: usize =
    32 / MAIN_CONTINUATION_WINDOW_PUBLICATION_LANES_PER_ROW;
pub(crate) const MAIN_CONTINUATION_WINDOW_PUBLICATION_SUBBLOCKS_PER_TILE: usize =
    MAIN_CONTINUATION_WINDOW_ROWS_PER_TILE / MAIN_CONTINUATION_WINDOW_PUBLICATION_ROWS_PER_BLOCK;
pub(crate) const MAIN_CONTINUATION_WINDOW_PUBLICATION_BLOCKS_PER_TILE: usize =
    MAIN_CONTINUATION_WINDOW_SELECTOR_BLOCKS
        * MAIN_CONTINUATION_WINDOW_PUBLICATION_SUBBLOCKS_PER_TILE;
pub(crate) const MAIN_CONTINUATION_WINDOW_ROWS_PER_TILE: usize = 32;
pub(crate) const MAIN_CONTINUATION_WINDOW_TENSOR_CELLS: usize = 27;
pub(crate) const MAIN_CONTINUATION_WINDOW_FOLD_COORDINATES: usize = 3;
pub(crate) const MAIN_CONTINUATION_WINDOW_FOLD_LIST_ENDPOINTS: usize =
    MAIN_CONTINUATION_WINDOW_WARPS + 1;

/// One semantic source's read and canonical publication lanes.
#[repr(C, align(2))]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct MainContinuationWindowSourceRecord {
    pub(crate) src: u16,
    pub(crate) publish: u16,
}

/// Complete by-value argument of one generated continuation-window kernel.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub(crate) struct MainContinuationWindowDesc {
    pub(crate) program: [u16; MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY],
    pub(crate) program_words: u16,
    pub(crate) source_count: u16,
    pub(crate) fold_list_offsets: [u16; MAIN_CONTINUATION_WINDOW_FOLD_LIST_ENDPOINTS],
    pub(crate) fold_sources: [u16; MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY],
    pub(crate) source:
        [MainContinuationWindowSourceRecord; MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY],
    pub(crate) slot: [BwdSegAddrSlot; MAIN_CONTINUATION_WINDOW_SOURCE_WINDOW_CAPACITY],
    pub(crate) c_init_coeff: u32,
    pub(crate) immediates: [u32; MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY],
    /// Coordinates folded by the publication prologue: zero for the R0
    /// depth-zero materializer, three for a continuation pass.
    pub(crate) publication_fold: u32,
    pub(crate) eq_low: *const E4,
    pub(crate) partials: *mut E4,
    pub(crate) row_tiles: u32,
    pub(crate) eq_sizes: GkrEqSizes,
}

const _: () = {
    assert!(MAIN_CONTINUATION_WINDOW_PROGRAM_WORD_CAPACITY == 6_472);
    assert!(MAIN_CONTINUATION_WINDOW_SOURCE_CAPACITY == 1_072);
    assert!(MAIN_CONTINUATION_WINDOW_SOURCE_WINDOW_CAPACITY == 64);
    assert!(MAIN_CONTINUATION_WINDOW_IMMEDIATE_CAPACITY == 512);
    assert!(MAIN_CONTINUATION_WINDOW_THREADS == 96);
    assert!(MAIN_CONTINUATION_WINDOW_PUBLICATION_THREADS == 96);
    assert!(MAIN_CONTINUATION_WINDOW_PUBLICATION_LANES_PER_ROW == 4);
    assert!(MAIN_CONTINUATION_WINDOW_PUBLICATION_ROWS_PER_BLOCK == 8);
    assert!(MAIN_CONTINUATION_WINDOW_PUBLICATION_SUBBLOCKS_PER_TILE == 4);
    assert!(MAIN_CONTINUATION_WINDOW_PUBLICATION_BLOCKS_PER_TILE == 12);
    assert!(
        MAIN_CONTINUATION_WINDOW_WARPS
            == MAIN_CONTINUATION_WINDOW_SELECTOR_BLOCKS * MAIN_CONTINUATION_WINDOW_BLOCK_WARPS
    );
    assert!(MAIN_CONTINUATION_WINDOW_TENSOR_CELLS == 3 * MAIN_CONTINUATION_WINDOW_WARPS);
    assert!(MAIN_CONTINUATION_WINDOW_ROWS_PER_TILE == 32);
    assert!(BWD_SEG_ADDR_NONE == SOURCE_NONE);

    assert!(size_of::<MainContinuationWindowSourceRecord>() == 4);
    assert!(align_of::<MainContinuationWindowSourceRecord>() == 2);
    assert!(offset_of!(MainContinuationWindowSourceRecord, src) == 0);
    assert!(offset_of!(MainContinuationWindowSourceRecord, publish) == 2);

    assert!(size_of::<MainContinuationWindowDesc>() == 22_512);
    assert!(align_of::<MainContinuationWindowDesc>() == DESCRIPTOR_ALIGNMENT_BYTES);
    assert!(size_of::<MainContinuationWindowDesc>() <= KERNEL_ARGUMENT_CEILING_BYTES);
    assert!(offset_of!(MainContinuationWindowDesc, program) == 0);
    assert!(offset_of!(MainContinuationWindowDesc, program_words) == 12_944);
    assert!(offset_of!(MainContinuationWindowDesc, source_count) == 12_946);
    assert!(offset_of!(MainContinuationWindowDesc, fold_list_offsets) == 12_948);
    assert!(offset_of!(MainContinuationWindowDesc, fold_sources) == 12_968);
    assert!(offset_of!(MainContinuationWindowDesc, source) == 15_112);
    assert!(offset_of!(MainContinuationWindowDesc, slot) == 19_400);
    assert!(offset_of!(MainContinuationWindowDesc, c_init_coeff) == 20_424);
    assert!(offset_of!(MainContinuationWindowDesc, immediates) == 20_428);
    assert!(offset_of!(MainContinuationWindowDesc, publication_fold) == 22_476);
    assert!(offset_of!(MainContinuationWindowDesc, eq_low) == 22_480);
    assert!(offset_of!(MainContinuationWindowDesc, partials) == 22_488);
    assert!(offset_of!(MainContinuationWindowDesc, row_tiles) == 22_496);
    assert!(offset_of!(MainContinuationWindowDesc, eq_sizes) == 22_500);
    assert!(size_of::<MainContinuationWindowDesc>().is_multiple_of(DESCRIPTOR_ALIGNMENT_BYTES));
    assert!(BWD_SEG_C_INIT_NONE == u32::MAX);
};

#[cfg(test)]
mod cpu_main_continuation_binding {
    use core::mem::{align_of, offset_of, size_of};

    use super::MainContinuationWindowDesc;

    const CUDA_ABI: &str = include_str!(
        "../../../native/gkr/backward/main_continuation_window/main_continuation_window_abi.cuh"
    );

    #[test]
    fn cpu_main_continuation_binding_abi_is_exact() {
        assert_eq!(size_of::<MainContinuationWindowDesc>(), 22_512);
        assert_eq!(align_of::<MainContinuationWindowDesc>(), 16);
        assert_eq!(offset_of!(MainContinuationWindowDesc, program), 0);
        assert_eq!(
            offset_of!(MainContinuationWindowDesc, program_words),
            12_944
        );
        assert_eq!(offset_of!(MainContinuationWindowDesc, source_count), 12_946);
        assert_eq!(
            offset_of!(MainContinuationWindowDesc, fold_list_offsets),
            12_948
        );
        assert_eq!(offset_of!(MainContinuationWindowDesc, fold_sources), 12_968);
        assert_eq!(offset_of!(MainContinuationWindowDesc, source), 15_112);
        assert_eq!(offset_of!(MainContinuationWindowDesc, slot), 19_400);
        assert_eq!(offset_of!(MainContinuationWindowDesc, c_init_coeff), 20_424);
        assert_eq!(offset_of!(MainContinuationWindowDesc, immediates), 20_428);
        assert_eq!(
            offset_of!(MainContinuationWindowDesc, publication_fold),
            22_476
        );
        assert_eq!(offset_of!(MainContinuationWindowDesc, eq_low), 22_480);
        assert_eq!(offset_of!(MainContinuationWindowDesc, partials), 22_488);
        assert_eq!(offset_of!(MainContinuationWindowDesc, row_tiles), 22_496);
        assert_eq!(offset_of!(MainContinuationWindowDesc, eq_sizes), 22_500);
    }

    #[test]
    fn cpu_main_continuation_binding_cuda_abi_pins_every_tail_field() {
        for assertion in [
            "sizeof(bwd_main_cont_window_desc) == 22512",
            "alignof(bwd_main_cont_window_desc) == 16",
            "__builtin_offsetof(bwd_main_cont_window_desc, publication_fold) == 22476",
            "__builtin_offsetof(bwd_main_cont_window_desc, eq_low) == 22480",
            "__builtin_offsetof(bwd_main_cont_window_desc, partials) == 22488",
            "__builtin_offsetof(bwd_main_cont_window_desc, row_tiles) == 22496",
            "__builtin_offsetof(bwd_main_cont_window_desc, eq_sizes) == 22500",
        ] {
            assert!(
                CUDA_ABI.contains(assertion),
                "missing CUDA assertion {assertion}"
            );
        }
    }
}
