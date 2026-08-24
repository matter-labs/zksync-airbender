//! Exact descriptor binding and enqueue-only launch for the main-layer tail.

use core::marker::PhantomData;
use core::mem::{align_of, offset_of, size_of};

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::static_host::{alloc_static_pinned_box_from_slice, StaticPinnedBox};
use gpu_gkr_compiler::{SourceId, KERNEL_ARGUMENT_CEILING_BYTES};
use gpu_prover_context::ProverContext;

use super::{
    MainTailProgram, MAIN_TAIL_BLOB_ALIGNMENT, MAIN_TAIL_BLOB_BYTES, MAIN_TAIL_IMMEDIATE_CAPACITY,
    MAIN_TAIL_IMMEDIATE_OFFSET, MAIN_TAIL_K, MAIN_TAIL_LIST_OFFSETS, MAIN_TAIL_LIST_OFFSETS_OFFSET,
    MAIN_TAIL_PROGRAM_OFFSET, MAIN_TAIL_PROGRAM_WORD_CAPACITY, MAIN_TAIL_SOURCE_CAPACITY,
};
use crate::backward::main_continuation::{
    ContinuationPublicationError, ContinuationPublishedLevel, ContinuationPublishedShape,
};
use crate::backward::main_layer::execution_plan::MainEqBoundaryWitness;
use crate::backward::{make_eq_sizes, GkrEqSizes};
use crate::upstream::PrimeField;

pub(crate) const MAIN_TAIL_BLOCK_THREADS: u32 = 256;
pub(crate) const MAIN_TAIL_DESCRIPTOR_BYTES: usize = 128;
pub(crate) const MAIN_TAIL_PARAMETER_HEADROOM: usize =
    KERNEL_ARGUMENT_CEILING_BYTES - MAIN_TAIL_DESCRIPTOR_BYTES;

/// Rust half of `bwd_main_tail_desc`. The fixed program blob stays in device
/// memory and this exact 128-byte descriptor is passed by value.
#[repr(C, align(16))]
#[derive(Clone, Copy, Debug)]
pub(crate) struct MainTailDesc {
    pub(crate) program_blob: *const u8,
    pub(crate) entry: *const E4,
    pub(crate) ping: *mut E4,
    pub(crate) pong: *mut E4,
    pub(crate) eq_low: *mut E4,
    pub(crate) prev_claim_coordinates: *const E4,
    pub(crate) seed: *mut u32,
    pub(crate) claim: *mut E4,
    pub(crate) eq_prefactor: *mut E4,
    pub(crate) coefficients_out: *mut E4,
    pub(crate) challenges_out: *mut E4,
    pub(crate) eq_sizes: GkrEqSizes,
    pub(crate) entry_column_elems: u32,
    pub(crate) source_count: u16,
    pub(crate) program_words: u16,
    pub(crate) immediate_count: u16,
    pub(crate) c_init_coeff_id: u16,
    pub(crate) tail_start: u8,
    pub(crate) folding_steps: u8,
    pub(crate) k: u8,
    pub(crate) reserved: u8,
    pub(crate) blob_bytes: u32,
    pub(crate) tail_padding: [u8; 8],
}

const _: () = {
    assert!(size_of::<MainTailDesc>() == MAIN_TAIL_DESCRIPTOR_BYTES);
    assert!(align_of::<MainTailDesc>() == 16);
    assert!(offset_of!(MainTailDesc, program_blob) == 0);
    assert!(offset_of!(MainTailDesc, entry) == 8);
    assert!(offset_of!(MainTailDesc, ping) == 16);
    assert!(offset_of!(MainTailDesc, pong) == 24);
    assert!(offset_of!(MainTailDesc, eq_low) == 32);
    assert!(offset_of!(MainTailDesc, prev_claim_coordinates) == 40);
    assert!(offset_of!(MainTailDesc, seed) == 48);
    assert!(offset_of!(MainTailDesc, claim) == 56);
    assert!(offset_of!(MainTailDesc, eq_prefactor) == 64);
    assert!(offset_of!(MainTailDesc, coefficients_out) == 72);
    assert!(offset_of!(MainTailDesc, challenges_out) == 80);
    assert!(offset_of!(MainTailDesc, eq_sizes) == 88);
    assert!(offset_of!(MainTailDesc, entry_column_elems) == 100);
    assert!(offset_of!(MainTailDesc, source_count) == 104);
    assert!(offset_of!(MainTailDesc, program_words) == 106);
    assert!(offset_of!(MainTailDesc, immediate_count) == 108);
    assert!(offset_of!(MainTailDesc, c_init_coeff_id) == 110);
    assert!(offset_of!(MainTailDesc, tail_start) == 112);
    assert!(offset_of!(MainTailDesc, folding_steps) == 113);
    assert!(offset_of!(MainTailDesc, k) == 114);
    assert!(offset_of!(MainTailDesc, reserved) == 115);
    assert!(offset_of!(MainTailDesc, blob_bytes) == 116);
    assert!(offset_of!(MainTailDesc, tail_padding) == 120);
    assert!(MAIN_TAIL_PARAMETER_HEADROOM == 32_636);
};

#[derive(Clone, Copy, Debug)]
pub(crate) struct MainTailRuntimeState {
    pub(crate) eq_low: *mut E4,
    pub(crate) prev_claim_coordinates: *const E4,
    pub(crate) seed: *mut u32,
    pub(crate) claim: *mut E4,
    pub(crate) eq_prefactor: *mut E4,
    pub(crate) coefficients_out: *mut E4,
    pub(crate) challenges_out: *mut E4,
}

#[derive(Debug)]
pub(crate) enum MainTailBindError {
    Cuda(era_cudart_sys::CudaError),
    Publication(ContinuationPublicationError),
    ProgramLayerMismatch {
        expected: usize,
        actual: usize,
    },
    ProgramShape {
        resource: &'static str,
        required: usize,
        capacity: usize,
    },
    InvalidGeometry {
        tail_start: usize,
        folding_steps: usize,
    },
    EntryShape {
        expected: ContinuationPublishedShape,
        actual: ContinuationPublishedShape,
    },
    EqBoundaryConsumer {
        expected: u8,
        actual: u8,
    },
    EqBoundarySuffix {
        expected: u8,
        actual: u8,
    },
    EqBoundarySizes {
        expected: GkrEqSizes,
        actual: GkrEqSizes,
    },
    NullRuntimePointer {
        resource: &'static str,
    },
    FinalAllocationLength {
        required: usize,
        available: usize,
    },
    AllocationSizeOverflow,
}

impl From<era_cudart_sys::CudaError> for MainTailBindError {
    fn from(error: era_cudart_sys::CudaError) -> Self {
        Self::Cuda(error)
    }
}

impl From<ContinuationPublicationError> for MainTailBindError {
    fn from(error: ContinuationPublicationError) -> Self {
        Self::Publication(error)
    }
}

impl core::fmt::Display for MainTailBindError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for MainTailBindError {}

/// Serialize exactly one fixed tail blob. The zero initialization is the sole
/// source of every reserved byte. Canonical compiler immediates cross the ABI
/// only after conversion to reduced Montgomery words.
pub(crate) fn serialize_main_tail_program_blob(
    program: &MainTailProgram,
) -> [u8; MAIN_TAIL_BLOB_BYTES] {
    let mut blob = [0u8; MAIN_TAIL_BLOB_BYTES];
    for (index, &list_offset) in program.list_offsets.iter().enumerate() {
        let offset = MAIN_TAIL_LIST_OFFSETS_OFFSET + index * size_of::<u16>();
        blob[offset..offset + size_of::<u16>()].copy_from_slice(&list_offset.to_le_bytes());
    }
    for (index, &word) in program.program_words.iter().enumerate() {
        let offset = MAIN_TAIL_PROGRAM_OFFSET + index * size_of::<u16>();
        blob[offset..offset + size_of::<u16>()].copy_from_slice(&word.to_le_bytes());
    }
    for (index, &canonical) in program.immediates.iter().enumerate() {
        let raw = BF::from_u32_with_reduction(canonical).as_u32_raw_repr_reduced();
        let offset = MAIN_TAIL_IMMEDIATE_OFFSET + index * size_of::<u32>();
        blob[offset..offset + size_of::<u32>()].copy_from_slice(&raw.to_le_bytes());
    }
    blob
}

cuda_kernel!(
    GkrBwdMainTail,
    ab_gkr_bwd_main_tail_kernel(desc: MainTailDesc)
);

/// Prepared owner. The incoming publication stays borrowed until enqueue.
pub(crate) struct MainTailLaunch<'input> {
    desc: MainTailDesc,
    tail_rounds: usize,
    final_shape: ContinuationPublishedShape,
    ping_pong_elems: usize,
    final_elems: usize,
    program_blob_host: StaticPinnedBox<u8>,
    program_blob_device: DeviceAllocation<u8>,
    ping: DeviceAllocation<E4>,
    pong: DeviceAllocation<E4>,
    _entry_keepalive: PhantomData<&'input ContinuationPublishedLevel>,
}

/// Fully published ownership prepared before the sole CUDA enqueue.
struct PreparedMainTailLaunch<'input> {
    desc: MainTailDesc,
    final_level: ContinuationPublishedLevel,
    scratch: DeviceAllocation<E4>,
    program_blob_host: StaticPinnedBox<u8>,
    program_blob_device: DeviceAllocation<u8>,
    _entry_keepalive: PhantomData<&'input ContinuationPublishedLevel>,
}

/// Launched ownership. The final buffer remains canonical and dense; the
/// other ping-pong buffer and program staging remain available as keepalives.
pub(crate) struct MainTailLaunched {
    final_level: ContinuationPublishedLevel,
    scratch: DeviceAllocation<E4>,
    program_blob_host: Option<StaticPinnedBox<u8>>,
    program_blob_device: DeviceAllocation<u8>,
}

impl MainTailLaunched {
    pub(crate) fn final_level(&self) -> &ContinuationPublishedLevel {
        &self.final_level
    }

    pub(crate) fn into_final_level(self) -> ContinuationPublishedLevel {
        self.final_level
    }

    pub(crate) fn take_host_staging(&mut self) -> Option<StaticPinnedBox<u8>> {
        self.program_blob_host.take()
    }

    pub(crate) fn scratch(&self) -> &DeviceAllocation<E4> {
        &self.scratch
    }

    pub(crate) fn program_blob_device(&self) -> &DeviceAllocation<u8> {
        &self.program_blob_device
    }
}

fn checked_geometry(
    tail_start: usize,
    folding_steps: usize,
) -> Result<(usize, usize), MainTailBindError> {
    let tail_rounds =
        folding_steps
            .checked_sub(tail_start)
            .ok_or(MainTailBindError::InvalidGeometry {
                tail_start,
                folding_steps,
            })?;
    if !(1..=6).contains(&tail_rounds) || tail_start < 3 || folding_steps > u8::MAX as usize {
        return Err(MainTailBindError::InvalidGeometry {
            tail_start,
            folding_steps,
        });
    }
    let entry_column_elems =
        8usize
            .checked_shl(tail_rounds as u32)
            .ok_or(MainTailBindError::InvalidGeometry {
                tail_start,
                folding_steps,
            })?;
    Ok((tail_rounds, entry_column_elems))
}

pub(crate) fn validate_main_tail_final_publication_capacity(
    required: usize,
    available: usize,
) -> Result<(), MainTailBindError> {
    if required > available {
        Err(MainTailBindError::FinalAllocationLength {
            required,
            available,
        })
    } else {
        Ok(())
    }
}

fn validate_program(program: &MainTailProgram) -> Result<(), MainTailBindError> {
    for (resource, required, capacity) in [
        (
            "list offsets",
            program.list_offsets.len(),
            MAIN_TAIL_LIST_OFFSETS,
        ),
        (
            "program words",
            program.program_words.len(),
            MAIN_TAIL_PROGRAM_WORD_CAPACITY,
        ),
        (
            "immediates",
            program.immediates.len(),
            MAIN_TAIL_IMMEDIATE_CAPACITY,
        ),
        (
            "sources",
            usize::from(program.source_count),
            MAIN_TAIL_SOURCE_CAPACITY,
        ),
    ] {
        if required > capacity {
            return Err(MainTailBindError::ProgramShape {
                resource,
                required,
                capacity,
            });
        }
    }
    if usize::from(program.k) != MAIN_TAIL_K
        || usize::from(program.list_offsets[MAIN_TAIL_K]) != program.program_words.len()
        || program.program_words.len() % 3 != 0
        || program.source_count == 0
    {
        return Err(MainTailBindError::ProgramShape {
            resource: "fixed tail wire",
            required: program.program_words.len(),
            capacity: MAIN_TAIL_PROGRAM_WORD_CAPACITY,
        });
    }
    Ok(())
}

fn require_pointer<T>(resource: &'static str, pointer: *const T) -> Result<(), MainTailBindError> {
    if pointer.is_null() {
        Err(MainTailBindError::NullRuntimePointer { resource })
    } else {
        Ok(())
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn bind_main_tail<'input>(
    expected_layer: usize,
    program: &MainTailProgram,
    entry: &'input ContinuationPublishedLevel,
    tail_start: usize,
    folding_steps: usize,
    eq_boundary: MainEqBoundaryWitness,
    runtime: MainTailRuntimeState,
    context: &ProverContext,
) -> Result<MainTailLaunch<'input>, MainTailBindError> {
    validate_program(program)?;
    if program.layer != expected_layer {
        return Err(MainTailBindError::ProgramLayerMismatch {
            expected: expected_layer,
            actual: program.layer,
        });
    }
    let (tail_rounds, entry_column_elems) = checked_geometry(tail_start, folding_steps)?;
    let final_shape = ContinuationPublishedShape {
        depth: (folding_steps - 1) as u8,
        columns: usize::from(program.source_count),
        column_elems: 2,
    };
    let ping_pong_elems = usize::from(program.source_count)
        .checked_mul(entry_column_elems >> 3)
        .ok_or(MainTailBindError::AllocationSizeOverflow)?;
    let final_elems = final_shape
        .columns
        .checked_mul(final_shape.column_elems)
        .ok_or(MainTailBindError::AllocationSizeOverflow)?;
    validate_main_tail_final_publication_capacity(final_elems, ping_pong_elems)?;
    let expected_shape = ContinuationPublishedShape {
        depth: (tail_start - 3) as u8,
        columns: usize::from(program.source_count),
        column_elems: entry_column_elems,
    };
    if entry.shape() != expected_shape {
        return Err(MainTailBindError::EntryShape {
            expected: expected_shape,
            actual: entry.shape(),
        });
    }
    if eq_boundary.consumer_round != tail_start as u8 {
        return Err(MainTailBindError::EqBoundaryConsumer {
            expected: tail_start as u8,
            actual: eq_boundary.consumer_round,
        });
    }
    if eq_boundary.semantic_suffix_offset != tail_start as u8 + 1 {
        return Err(MainTailBindError::EqBoundarySuffix {
            expected: tail_start as u8 + 1,
            actual: eq_boundary.semantic_suffix_offset,
        });
    }
    let expected_eq_sizes = make_eq_sizes(tail_rounds - 1);
    if eq_boundary.eq_sizes != expected_eq_sizes
        || eq_boundary.eq_sizes.high != [0, 0]
        || eq_boundary.eq_sizes.low != (tail_rounds - 1) as u32
    {
        return Err(MainTailBindError::EqBoundarySizes {
            expected: expected_eq_sizes,
            actual: eq_boundary.eq_sizes,
        });
    }
    for (resource, pointer) in [
        ("eq_low", runtime.eq_low.cast_const().cast::<u8>()),
        (
            "previous claim coordinates",
            runtime.prev_claim_coordinates.cast::<u8>(),
        ),
        ("seed", runtime.seed.cast_const().cast::<u8>()),
        ("claim", runtime.claim.cast_const().cast::<u8>()),
        (
            "eq prefactor",
            runtime.eq_prefactor.cast_const().cast::<u8>(),
        ),
        (
            "coefficient output",
            runtime.coefficients_out.cast_const().cast::<u8>(),
        ),
        (
            "challenge output",
            runtime.challenges_out.cast_const().cast::<u8>(),
        ),
    ] {
        require_pointer(resource, pointer)?;
    }

    let mut ping = context.alloc(ping_pong_elems, AllocationPlacement::BestFit)?;
    let mut pong = context.alloc(ping_pong_elems, AllocationPlacement::BestFit)?;

    let blob = serialize_main_tail_program_blob(program);
    debug_assert!(blob
        [MAIN_TAIL_PROGRAM_OFFSET + program.program_words.len() * 2..MAIN_TAIL_IMMEDIATE_OFFSET]
        .iter()
        .all(|&byte| byte == 0));
    debug_assert!(
        blob[MAIN_TAIL_IMMEDIATE_OFFSET + program.immediates.len() * 4..]
            .iter()
            .all(|&byte| byte == 0)
    );
    let program_blob_host = alloc_static_pinned_box_from_slice(&blob)?;
    let mut program_blob_device =
        context.alloc(MAIN_TAIL_BLOB_BYTES, AllocationPlacement::BestFit)?;
    memory_copy_async(
        &mut program_blob_device[..],
        &program_blob_host[..],
        context.get_exec_stream(),
    )?;

    let desc = MainTailDesc {
        program_blob: program_blob_device.as_ptr(),
        entry: entry.as_ptr(),
        ping: ping.as_mut_ptr(),
        pong: pong.as_mut_ptr(),
        eq_low: runtime.eq_low,
        prev_claim_coordinates: runtime.prev_claim_coordinates,
        seed: runtime.seed,
        claim: runtime.claim,
        eq_prefactor: runtime.eq_prefactor,
        coefficients_out: runtime.coefficients_out,
        challenges_out: runtime.challenges_out,
        eq_sizes: eq_boundary.eq_sizes,
        entry_column_elems: entry_column_elems as u32,
        source_count: program.source_count,
        program_words: program.program_words.len() as u16,
        immediate_count: program.immediates.len() as u16,
        c_init_coeff_id: program.c_init_coeff_id,
        tail_start: tail_start as u8,
        folding_steps: folding_steps as u8,
        k: program.k,
        reserved: 0,
        blob_bytes: MAIN_TAIL_BLOB_BYTES as u32,
        tail_padding: [0; 8],
    };
    Ok(MainTailLaunch {
        desc,
        tail_rounds,
        final_shape,
        ping_pong_elems,
        final_elems,
        program_blob_host,
        program_blob_device,
        ping,
        pong,
        _entry_keepalive: PhantomData,
    })
}

fn prepare_main_tail_launch(
    launch: MainTailLaunch<'_>,
) -> Result<PreparedMainTailLaunch<'_>, MainTailBindError> {
    let (mut final_allocation, scratch) = if launch.tail_rounds % 2 == 1 {
        (launch.ping, launch.pong)
    } else {
        (launch.pong, launch.ping)
    };
    assert_eq!(final_allocation.len(), launch.ping_pong_elems);
    final_allocation.shrink_len_to(launch.final_elems);
    assert_eq!(final_allocation.len(), launch.final_elems);
    let publication =
        (0..launch.final_shape.columns).map(|source| (SourceId(source as u32), source));
    let final_level =
        ContinuationPublishedLevel::try_new(launch.final_shape, final_allocation, publication)?;
    Ok(PreparedMainTailLaunch {
        desc: launch.desc,
        final_level,
        scratch,
        program_blob_host: launch.program_blob_host,
        program_blob_device: launch.program_blob_device,
        _entry_keepalive: launch._entry_keepalive,
    })
}

fn enqueue_prepared_main_tail(
    prepared: PreparedMainTailLaunch<'_>,
    context: &ProverContext,
) -> Result<MainTailLaunched, MainTailBindError> {
    let config = CudaLaunchConfig::basic(1, MAIN_TAIL_BLOCK_THREADS, context.get_exec_stream());
    GkrBwdMainTailFunction::default()
        .launch(&config, &GkrBwdMainTailArguments::new(prepared.desc))?;
    Ok(MainTailLaunched {
        final_level: prepared.final_level,
        scratch: prepared.scratch,
        program_blob_host: Some(prepared.program_blob_host),
        program_blob_device: prepared.program_blob_device,
    })
}

/// Prepare exact publication ownership, enqueue the sole kernel, and return it.
pub(crate) fn launch_main_tail(
    launch: MainTailLaunch<'_>,
    context: &ProverContext,
) -> Result<MainTailLaunched, MainTailBindError> {
    let prepared = prepare_main_tail_launch(launch)?;
    enqueue_prepared_main_tail(prepared, context)
}

const _: () = {
    assert!(MAIN_TAIL_LIST_OFFSETS_OFFSET == 0);
    assert!(MAIN_TAIL_PROGRAM_OFFSET == 18);
    assert!(MAIN_TAIL_IMMEDIATE_OFFSET == 12_964);
    assert!(MAIN_TAIL_BLOB_BYTES == 15_024);
    assert!(MAIN_TAIL_BLOB_BYTES.is_multiple_of(MAIN_TAIL_BLOB_ALIGNMENT));
};
