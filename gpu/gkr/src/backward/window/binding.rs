//! Shared window-3 wire constants, row geometry, and source-lane binding helpers.
//!
//! The matching shared CUDA constants live in
//! `native/gkr/backward/window/window_abi.cuh`.

use crate::backward::window::bank::family_read_place;
use crate::backward::window::common::{
    BWD_COEFF_ORIGIN_PROCEDURAL, BWD_COEFF_ORIGIN_READ_BASE, BWD_COEFF_ORIGIN_READ_EXT,
    BWD_COEFF_PROCEDURAL_KINDS, BWD_COEFF_PROCEDURAL_NONE,
};
use crate::forward::vm::lower_common::{read_place_to_gkr_address, ResolvedColumn};
use crate::upstream::FieldKind;
use core::mem::size_of;

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

/// The window's runtime addressing: one slot per storage chunk actually read,
/// and the lane each source slot resolved to.
pub(crate) struct WindowAddressing {
    pub(crate) slots: Vec<BwdSourceWindow>,
    /// Indexed by source slot id; `None` for a source no window binds.
    pub(crate) lanes: Vec<Option<u16>>,
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
pub(crate) fn intern_window_addressing<B, E>(
    program: &WindowProgram,
    resolve_column: impl Fn(GKRAddress) -> Option<ResolvedColumn>,
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
            size_of::<E>()
        } else {
            size_of::<B>()
        } as u32;
        for column in &entry.columns {
            let place = family_read_place(entry.family, column.column)
                .expect("an addressless window is procedural");
            let address = read_place_to_gkr_address(&place);
            let resolved = resolve_column(address)
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
