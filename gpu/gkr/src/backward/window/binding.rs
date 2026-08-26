//! Rust half of the window-3 executor's launch ABI, plus the runtime binder
//! that turns a static [`WindowProgram`] into a launch-ready descriptor.
//!
//! The matching CUDA definitions and offset assertions live in
//! `native/gkr/backward/window/window_abi.cuh`.

use core::mem::{align_of, offset_of, size_of};

use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::{
    WindowProgram, DESCRIPTOR_ALIGNMENT_BYTES, KERNEL_ARGUMENT_CEILING_BYTES, LEAN_MAX_IMMEDIATES,
    MAX_SOURCE_WINDOWS, SOURCE_WINDOW_COLUMNS, WINDOW_SECTION_WORDS, WINDOW_SHAPE_DEFINED_BITS,
};
use gpu_prover_context::ProverContext;

use super::generated_registry::{
    GkrBwdR0Window3Arguments, GkrBwdR0Window3Signature, WindowKernelEntry,
    WINDOWED_R0_BLOCK_THREADS, WINDOWED_R0_DISPATCH, WINDOWED_R0_KERNELS,
    WINDOWED_R0_UNIVERSAL_MASK,
};
use super::tail::WINDOW_TAIL_TENSOR_CELLS;
use crate::backward::window::bank::family_read_place;
use crate::backward::window::common::{
    BwdSourceWindow, BWD_COEFF_ORIGIN_PROCEDURAL, BWD_COEFF_ORIGIN_READ_BASE,
    BWD_COEFF_ORIGIN_READ_EXT, BWD_COEFF_PROCEDURAL_KINDS, BWD_COEFF_PROCEDURAL_NONE,
    BWD_SOURCE_LANE_COLUMN_BITS,
};
use crate::backward::window::zeroed_box;
use crate::backward::{make_eq_sizes, GkrEqSizes, GKR_EQ_GROUP_SIZE, GKR_EQ_HIGH_SLOTS};
use crate::forward::vm::lower::read_place_to_gkr_address;
use crate::forward::vm::production_bind::resolve_storage_column;
use crate::upstream::{FieldKind, GKRAddress};
use crate::GpuGKRStorage;

pub(crate) const BWD_WINDOW_ADDR_SLOTS: usize = MAX_SOURCE_WINDOWS;
pub(crate) const BWD_WINDOW_SECTION_WORDS: usize = WINDOW_SECTION_WORDS;
pub(crate) const BWD_WINDOW_MAX_IMMEDIATES: usize = LEAN_MAX_IMMEDIATES;
/// opcode, factor, source_a, source_b.
pub(crate) const BWD_WINDOW_INSTRUCTION_WORDS: usize = 4;
/// Retained-corpus maximum 7,036 words, rounded so the array is a whole number
/// of 16-byte lines.
pub(crate) const BWD_WINDOW_PROGRAM_WORD_CAP: usize = 7_040;

/// Trace coordinates one window peels, so `2^3` trace rows per window row.
pub(crate) const BWD_WINDOW_COORDINATES: usize = 3;
/// Window rows one block reduces into one 27-cell tensor.
pub(crate) const BWD_WINDOW_ROWS_PER_TILE: usize = 32;
/// The row axis a window leaves for the eq state is at most the three eq groups
/// the factored-eq layout carries.
pub(crate) const BWD_WINDOW_MAX_FOLDING_STEPS: usize =
    BWD_WINDOW_COORDINATES + GKR_EQ_GROUP_SIZE * (GKR_EQ_HIGH_SLOTS + 1);

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
    UndefinedShapeBits {
        bits: u16,
    },
    NoKernelForMask {
        mask: u16,
    },
    DispatchBoundMismatch {
        mask: u16,
        ruled: u32,
        compiled: u32,
    },
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

/// The layer-scoped runtime addresses a window launch binds.
#[derive(Clone, Copy, Debug)]
pub(crate) struct WindowRuntimeScratch {
    /// Production factored-eq low table; the high tables stay in `ab_gkr_eq_high`.
    pub eq_low: *const E4,
    /// The layer's shared partials buffer, sized by [`window_partials_len`].
    pub partials: *mut E4,
    pub partials_capacity: usize,
}

/// A launch-ready window producer.
pub(crate) struct WindowLaunch {
    pub binding: Box<WindowLaunchBinding>,
    pub kernel: &'static WindowKernelEntry,
    pub row_tiles: usize,
    /// The split tail's 27-cell scratch, past the partial tensor.
    pub reduced_tensor: *mut E4,
}

/// Resolve a lowered shape mask to its generated kernel: the ruled compiled mask
/// if the manifest names the shape, the universal kernel if it does not, and a
/// typed rejection if the mask carries a feature bit no kernel has heard of.
pub(crate) fn resolve_window_kernel(
    mask: u16,
) -> Result<&'static WindowKernelEntry, WindowBindError> {
    if mask & !WINDOW_SHAPE_DEFINED_BITS != 0 {
        return Err(WindowBindError::UndefinedShapeBits { bits: mask });
    }
    let (compiled, ruled_min_blocks) = WINDOWED_R0_DISPATCH
        .iter()
        .find(|(native, ..)| *native == mask)
        .map(|(_, compiled, min_blocks)| (*compiled, *min_blocks))
        .unwrap_or((WINDOWED_R0_UNIVERSAL_MASK, 0));
    let entry = WINDOWED_R0_KERNELS
        .iter()
        .find(|entry| entry.mask == compiled)
        .ok_or(WindowBindError::NoKernelForMask { mask: compiled })?;
    if ruled_min_blocks != 0 && ruled_min_blocks != entry.min_blocks {
        return Err(WindowBindError::DispatchBoundMismatch {
            mask,
            ruled: ruled_min_blocks,
            compiled: entry.min_blocks,
        });
    }
    Ok(entry)
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
        if let Some(index) = self.slots.iter().position(|entry| {
            entry.base == slot.base
                && entry.log2_stride == slot.log2_stride
                && entry.origin == slot.origin
                && entry.procedural_kind == slot.procedural_kind
        }) {
            return Ok(index);
        }
        if self.slots.len() == BWD_WINDOW_ADDR_SLOTS {
            return Err(WindowBindError::Capacity {
                resource: "window address slots",
                required: BWD_WINDOW_ADDR_SLOTS + 1,
                capacity: BWD_WINDOW_ADDR_SLOTS,
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

/// The addressing rule a window slot expresses: a column's rank inside its
/// matrix splits into the chunk of [`SOURCE_WINDOW_COLUMNS`] columns the slot
/// bases at, and the column's index within that chunk. Same split as
/// `production_bind::SlotTable::intern`, which is what makes two columns of one
/// artifact window in different matrices simply two slots.
pub(super) fn window_chunk_address(matrix: usize, pointer: usize, stride: usize) -> (usize, usize) {
    let rank = (pointer - matrix) / stride;
    let chunk = rank / SOURCE_WINDOW_COLUMNS;
    (
        matrix + chunk * SOURCE_WINDOW_COLUMNS * stride,
        rank % SOURCE_WINDOW_COLUMNS,
    )
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
fn intern_window_addressing<E: Copy>(
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
                reserved: [0; 5],
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
                reserved: [0; 5],
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
    binding.program[..program.words.len()].copy_from_slice(&program.words);
    // The wire's lowered lanes are the artifact's geometry; the side table names
    // every word that carries one, so each is rewritten to the lane storage
    // actually implies.
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
        *binding
            .program
            .get_mut(word)
            .ok_or(WindowBindError::LaneSourceMissing {
                word: lane.word,
                source: lane.source,
            })? = runtime;
    }
    binding.immediates[..program.immediates.len()].copy_from_slice(&program.immediates);
    Ok(binding)
}

/// Bind a lowered window program to production storage and the layer's scratch.
pub(crate) fn bind_window_launch<E: Copy>(
    program: &WindowProgram,
    storage: &GpuGKRStorage<BF, E>,
    folding_steps: usize,
    scratch: WindowRuntimeScratch,
) -> Result<WindowLaunch, WindowBindError> {
    let addressing = intern_window_addressing(storage, program)?;
    let kernel = resolve_window_kernel(program.shape.bits())?;
    let binding = build_window_binding(program, &addressing, folding_steps, scratch)?;
    let row_tiles = window_row_tiles(1usize << folding_steps);
    // SAFETY: the capacity check above covers the tensor past the partials.
    let reduced_tensor = unsafe { scratch.partials.add(WINDOW_TAIL_TENSOR_CELLS * row_tiles) };
    Ok(WindowLaunch {
        binding,
        kernel,
        row_tiles,
        reduced_tensor,
    })
}

/// A resolved registry entry IS the kernel function: the generated
/// `GkrBwdR0Window3Function` wrapper's tuple field is private to its own module,
/// so dispatch launches through the entry that named the symbol.
impl KernelFunction for WindowKernelEntry {
    type Signature = GkrBwdR0Window3Signature;

    fn as_ptr(&self) -> *const std::os::raw::c_void {
        self.symbol as *const std::os::raw::c_void
    }
}

/// Launch the window producer: one block per row tile, nine warps each.
pub(crate) fn launch_window_program(
    launch: &WindowLaunch,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = CudaLaunchConfig::basic(
        launch.row_tiles as u32,
        WINDOWED_R0_BLOCK_THREADS,
        context.get_exec_stream(),
    );
    launch
        .kernel
        .launch(&config, &GkrBwdR0Window3Arguments::new(*launch.binding))
}
