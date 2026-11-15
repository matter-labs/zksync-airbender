//! Shared window-3 wire constants, row geometry, and source-lane binding helpers.
//!
//! The matching shared CUDA constants live in
//! `native/gkr/backward/window/window_abi.cuh`.

pub(crate) use gpu_gkr_compiler::window::WINDOW_PROGRAM_WORD_CAP as BWD_WINDOW_PROGRAM_WORD_CAP;
use gpu_gkr_compiler::{
    WindowProgram, LEAN_MAX_IMMEDIATES, MAX_SOURCE_WINDOWS, SOURCE_WINDOW_COLUMNS,
    WINDOW_SECTION_WORDS,
};

use crate::backward::window::common::BwdSourceWindow;
use crate::backward::window::common::BWD_SOURCE_LANE_COLUMN_BITS;
use crate::backward::window::tail::WINDOW_TAIL_TENSOR_CELLS;
use crate::backward::GKR_EQ_GROUP_SIZE;
use crate::backward::GKR_EQ_HIGH_SLOTS;
use crate::upstream::GKRAddress;

pub(crate) const BWD_WINDOW_ADDR_SLOTS: usize = MAX_SOURCE_WINDOWS;
pub(crate) const BWD_WINDOW_SECTION_WORDS: usize = WINDOW_SECTION_WORDS;
pub(crate) const BWD_WINDOW_MAX_IMMEDIATES: usize = LEAN_MAX_IMMEDIATES;
/// opcode, factor, source_a, source_b.
pub(crate) const BWD_WINDOW_INSTRUCTION_WORDS: usize = 4;

/// Trace coordinates one window peels, so `2^3` trace rows per window row.
pub(crate) const BWD_WINDOW_COORDINATES: usize = 3;
/// Window rows one block reduces into one 27-cell tensor.
pub(crate) const BWD_WINDOW_ROWS_PER_TILE: usize = 32;
/// The row axis a window leaves for the eq state is at most the three eq groups
/// the factored-eq layout carries.
pub(crate) const BWD_WINDOW_MAX_FOLDING_STEPS: usize =
    BWD_WINDOW_COORDINATES + GKR_EQ_GROUP_SIZE * (GKR_EQ_HIGH_SLOTS + 1);

// ── Row geometry ─────────────────────────────────────────────────────────────

/// Coordinates the eq state still carries once the window peels its three: the
/// window's own row axis.
pub(crate) fn window_log_rows(folding_steps: usize) -> u32 {
    (folding_steps - BWD_WINDOW_COORDINATES) as u32
}

/// Blocks the window producer runs, one per 32 window rows.
pub(crate) fn window_row_tiles(trace_len: usize) -> usize {
    (trace_len >> BWD_WINDOW_COORDINATES)
        .div_ceil(BWD_WINDOW_ROWS_PER_TILE)
        .max(1)
}

/// The window's claim on the layer's shared partials buffer: the row-tile-major
/// partial tensor plus the 27 cells produced by its split tail.
pub(crate) fn window_partials_len(trace_len: usize) -> usize {
    WINDOW_TAIL_TENSOR_CELLS * (window_row_tiles(trace_len) + 1)
}

// ── Binding ──────────────────────────────────────────────────────────────────

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum WindowBindError {
    Capacity {
        resource: &'static str,
        required: usize,
        capacity: usize,
    },
    UnsupportedFoldingSteps {
        folding_steps: usize,
    },
    UnresolvedWindow {
        window: u8,
        address: GKRAddress,
    },
    WindowFieldMismatch {
        window: u8,
        expect_e4: bool,
    },
    WindowStrideMismatch {
        window: u8,
        stride_bytes: u32,
    },
    UnknownProceduralKind {
        window: u8,
        kind: u8,
    },
    EmptyWindow {
        window: u8,
    },
    /// A column's address is not a whole number of strides into its matrix, so
    /// it has no rank to address it by.
    UnresolvableRank {
        window: u8,
    },
    /// The wire reads a source the window identities never bound.
    LaneSourceMissing {
        word: u32,
        source: u16,
    },
}

impl core::fmt::Display for WindowBindError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for WindowBindError {}

pub(crate) fn window_lane(slot: usize, column: usize) -> u16 {
    ((slot << BWD_SOURCE_LANE_COLUMN_BITS) | column) as u16
}

/// The addressing rule a window slot expresses: a column's rank inside its
/// matrix splits into the chunk of [`SOURCE_WINDOW_COLUMNS`] columns the slot
/// bases at, and the column's index within that chunk. Same split as
/// `production_bind::SlotTable::intern`, which is what makes two columns of one
/// artifact window in different matrices simply two slots.
pub(crate) fn window_chunk_address(matrix: usize, pointer: usize, stride: usize) -> (usize, usize) {
    let rank = (pointer - matrix) / stride;
    let chunk = rank / SOURCE_WINDOW_COLUMNS;
    (
        matrix + chunk * SOURCE_WINDOW_COLUMNS * stride,
        rank % SOURCE_WINDOW_COLUMNS,
    )
}

pub(crate) fn intern_window_slot(
    slots: &mut Vec<BwdSourceWindow>,
    slot: BwdSourceWindow,
    capacity: usize,
) -> Option<usize> {
    if let Some(index) = slots.iter().position(|entry| {
        entry.base == slot.base
            && entry.log2_stride == slot.log2_stride
            && entry.r0_stride_bytes == slot.r0_stride_bytes
            && entry.origin == slot.origin
            && entry.procedural_kind == slot.procedural_kind
    }) {
        return Some(index);
    }
    if slots.len() == capacity {
        return None;
    }
    slots.push(slot);
    Some(slots.len() - 1)
}

pub(crate) fn bind_window_lane(lanes: &mut Vec<Option<u16>>, source: u32, lane: u16) {
    let source = source as usize;
    if source >= lanes.len() {
        lanes.resize(source + 1, None);
    }
    lanes[source] = Some(lane);
}

pub(crate) fn rewrite_window_words(
    program: &WindowProgram,
    lanes: &[Option<u16>],
    words: &mut [u16],
) -> Result<(), (u32, u16)> {
    words[..program.words.len()].copy_from_slice(&program.words);
    for lane in &program.source_lanes {
        let runtime = lanes
            .get(lane.source as usize)
            .copied()
            .flatten()
            .ok_or((lane.word, lane.source))?;
        *words
            .get_mut(lane.word as usize)
            .ok_or((lane.word, lane.source))? = runtime;
    }
    Ok(())
}
