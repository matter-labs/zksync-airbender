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
    LeanBoundWindow, WindowProgram, DESCRIPTOR_ALIGNMENT_BYTES, KERNEL_ARGUMENT_CEILING_BYTES,
    LEAN_MAX_IMMEDIATES, MAX_SOURCE_WINDOWS, SOURCE_WINDOW_COLUMNS, WINDOW_SECTION_WORDS,
    WINDOW_SHAPE_DEFINED_BITS,
};
use gpu_prover_context::ProverContext;

use super::generated_registry::{
    GkrBwdR0Window3Arguments, GkrBwdR0Window3Signature, WindowKernelEntry,
    WINDOWED_R0_BLOCK_THREADS, WINDOWED_R0_DISPATCH, WINDOWED_R0_FALLBACK_MASK,
    WINDOWED_R0_KERNELS,
};
use super::tail::WINDOW_TAIL_TENSOR_CELLS;
use crate::backward::vm::production_bind::family_read_place;
use crate::backward::vm::seg_desc::{
    BwdSegAddrSlot, BWD_COEFF_ORIGIN_PROCEDURAL, BWD_COEFF_ORIGIN_READ_BASE,
    BWD_COEFF_ORIGIN_READ_EXT, BWD_COEFF_PROCEDURAL_KINDS, BWD_COEFF_PROCEDURAL_NONE,
};
use crate::backward::vm::seg_lower::zeroed_box;
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

/// The window arm's claim on the layer's shared partials buffer: the row-tile-
/// major partial tensor, plus the 27 cells the split tail arm reduces it into.
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
    /// A referenced column does not sit at its wire-relative offset from the
    /// window's base: storage packing disagrees with the lowered geometry.
    NonContiguousWindow {
        window: u8,
        column: usize,
    },
    UnknownProceduralKind {
        window: u8,
        kind: u8,
    },
    EmptyWindow {
        window: u8,
    },
}

impl core::fmt::Display for WindowBindError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for WindowBindError {}

/// The layer-scoped runtime addresses a window launch binds.
#[allow(dead_code)] // The windowed scheduler path is the consumer.
#[derive(Clone, Copy, Debug)]
pub(crate) struct WindowRuntimeScratch {
    /// Production factored-eq low table; the high tables stay in `ab_gkr_eq_high`.
    pub eq_low: *const E4,
    /// The layer's shared partials buffer, sized by [`window_partials_len`].
    pub partials: *mut E4,
    pub partials_capacity: usize,
}

/// A launch-ready window producer.
#[allow(dead_code)] // The windowed scheduler path is the consumer.
pub(crate) struct WindowLaunch {
    pub binding: Box<WindowLaunchBinding>,
    pub kernel: &'static WindowKernelEntry,
    pub row_tiles: usize,
    /// The split tail arm's 27-cell scratch, past the partial tensor.
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
        .unwrap_or((WINDOWED_R0_FALLBACK_MASK, 0));
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

/// Resolve one lowered window's storage address.
///
/// The wire carries the compiler's own `(window, relative column)` lanes, so a
/// slot's base is the address of the window's first column and every referenced
/// column must sit at its own relative offset from it. Storage packing that
/// disagrees is rejected rather than mis-addressed.
fn window_address_slot<E: Copy>(
    storage: &GpuGKRStorage<BF, E>,
    index: u8,
    entry: &LeanBoundWindow,
) -> Result<BwdSegAddrSlot, WindowBindError> {
    if let Some(kind) = entry.procedural_kind() {
        if usize::from(kind) >= BWD_COEFF_PROCEDURAL_KINDS {
            return Err(WindowBindError::UnknownProceduralKind {
                window: index,
                kind,
            });
        }
        return Ok(BwdSegAddrSlot {
            base: std::ptr::null(),
            log2_stride: 0,
            origin: BWD_COEFF_ORIGIN_PROCEDURAL,
            procedural_kind: kind,
            reserved: [0; 5],
        });
    }

    let expect_e4 = entry.backing_field() == FieldKind::Ext;
    let element = if expect_e4 {
        size_of::<E4>()
    } else {
        size_of::<BF>()
    } as u32;
    let mut bound: Option<(usize, *mut u8, u32)> = None;
    for column in &entry.columns {
        let relative = column
            .column
            .checked_sub(entry.first_column)
            .filter(|relative| *relative < SOURCE_WINDOW_COLUMNS)
            .ok_or(WindowBindError::NonContiguousWindow {
                window: index,
                column: column.column,
            })?;
        let place = family_read_place(entry.family, column.column)
            .expect("an addressless window is procedural");
        let address = read_place_to_gkr_address(&place);
        let resolved =
            resolve_storage_column(storage, address).ok_or(WindowBindError::UnresolvedWindow {
                window: index,
                address,
            })?;
        if resolved.is_e4 != expect_e4 {
            return Err(WindowBindError::WindowFieldMismatch {
                window: index,
                expect_e4,
            });
        }
        if resolved.ptr.is_null()
            || !resolved.stride_bytes.is_multiple_of(element)
            || !(resolved.stride_bytes / element).is_power_of_two()
        {
            return Err(WindowBindError::WindowStrideMismatch {
                window: index,
                stride_bytes: resolved.stride_bytes,
            });
        }
        let base = (resolved.ptr as usize)
            .checked_sub(relative * resolved.stride_bytes as usize)
            .ok_or(WindowBindError::NonContiguousWindow {
                window: index,
                column: column.column,
            })?;
        match bound {
            None => bound = Some((base, resolved.matrix_base, resolved.stride_bytes)),
            Some(bound) if bound == (base, resolved.matrix_base, resolved.stride_bytes) => {}
            Some(_) => {
                return Err(WindowBindError::NonContiguousWindow {
                    window: index,
                    column: column.column,
                })
            }
        }
    }
    let (base, _, stride_bytes) = bound.ok_or(WindowBindError::EmptyWindow { window: index })?;
    Ok(BwdSegAddrSlot {
        base: base as *const u8,
        log2_stride: (stride_bytes / element).trailing_zeros() as u8,
        origin: if expect_e4 {
            BWD_COEFF_ORIGIN_READ_EXT
        } else {
            BWD_COEFF_ORIGIN_READ_BASE
        },
        procedural_kind: BWD_COEFF_PROCEDURAL_NONE,
        reserved: [0; 5],
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
    slots: &[BwdSegAddrSlot],
    folding_steps: usize,
    scratch: WindowRuntimeScratch,
) -> Result<Box<WindowLaunchBinding>, WindowBindError> {
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
    binding.immediates[..program.immediates.len()].copy_from_slice(&program.immediates);
    Ok(binding)
}

/// Bind a lowered window program to production storage and the layer's scratch.
#[allow(dead_code)] // The windowed scheduler path is the consumer.
pub(crate) fn bind_window_launch<E: Copy>(
    program: &WindowProgram,
    storage: &GpuGKRStorage<BF, E>,
    folding_steps: usize,
    scratch: WindowRuntimeScratch,
) -> Result<WindowLaunch, WindowBindError> {
    if program.windows.len() > BWD_WINDOW_ADDR_SLOTS {
        return Err(WindowBindError::Capacity {
            resource: "window address slots",
            required: program.windows.len(),
            capacity: BWD_WINDOW_ADDR_SLOTS,
        });
    }
    let mut slots = Vec::with_capacity(program.windows.len());
    for (index, entry) in program.windows.iter().enumerate() {
        slots.push(window_address_slot(storage, index as u8, entry)?);
    }
    let kernel = resolve_window_kernel(program.shape.bits())?;
    let binding = build_window_binding(program, &slots, folding_steps, scratch)?;
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
#[allow(dead_code)] // The windowed scheduler path is the consumer.
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
