//! Exact descriptor binding and enqueue-only launch for the main-layer tail.

use core::mem::{align_of, offset_of, size_of};

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::{SourceId, KERNEL_ARGUMENT_CEILING_BYTES};
use gpu_prover_context::ProverContext;

use super::program::{
    MainTailProgram, MAIN_TAIL_BLOB_ALIGNMENT, MAIN_TAIL_BLOB_BYTES, MAIN_TAIL_IMMEDIATE_CAPACITY,
    MAIN_TAIL_IMMEDIATE_OFFSET, MAIN_TAIL_K, MAIN_TAIL_LIST_OFFSETS, MAIN_TAIL_LIST_OFFSETS_OFFSET,
    MAIN_TAIL_PROGRAM_OFFSET, MAIN_TAIL_PROGRAM_WORD_CAPACITY, MAIN_TAIL_SOURCE_CAPACITY,
};
use crate::backward::main_continuation::{ContinuationPublishedLevel, ContinuationPublishedShape};
use crate::backward::main_layer::execution_plan::MainEqBoundaryWitness;
use crate::backward::{make_eq_sizes, GkrEqSizes};
use crate::upstream::PrimeField;

pub(crate) const MAIN_TAIL_BLOCK_THREADS: u32 = 256;
pub(crate) const MAIN_TAIL_DESCRIPTOR_BYTES: usize = 128;
pub(crate) const MAIN_TAIL_KERNEL_ARGUMENT_BYTES: usize =
    MAIN_TAIL_DESCRIPTOR_BYTES + MAIN_TAIL_BLOB_BYTES;

/// Rust half of `bwd_main_tail_desc`. This exact 128-byte descriptor and its
/// fixed program blob are passed by value as separate kernel arguments.
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
    pub(crate) tail_padding: [u8; 14],
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
    assert!(offset_of!(MainTailDesc, tail_padding) == 114);
    assert!(MAIN_TAIL_KERNEL_ARGUMENT_BYTES <= KERNEL_ARGUMENT_CEILING_BYTES);
};

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub(crate) struct MainTailProgramBlob {
    pub(crate) bytes: [u8; MAIN_TAIL_BLOB_BYTES],
}

const _: () = {
    assert!(size_of::<MainTailProgramBlob>() == MAIN_TAIL_BLOB_BYTES);
    assert!(align_of::<MainTailProgramBlob>() == MAIN_TAIL_BLOB_ALIGNMENT);
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
    ab_gkr_bwd_main_tail_kernel(desc: MainTailDesc, program_blob: MainTailProgramBlob)
);

/// Prepared owner. The incoming publication is owned until the sole enqueue,
/// so a bound tail cannot outlive or skip its real entry.
pub(crate) struct MainTailLaunch {
    desc: MainTailDesc,
    tail_rounds: usize,
    final_shape: ContinuationPublishedShape,
    ping_pong_elems: usize,
    final_elems: usize,
    program_blob: MainTailProgramBlob,
    ping: DeviceAllocation<E4>,
    pong: DeviceAllocation<E4>,
    entry_keepalive: ContinuationPublishedLevel,
}

/// Fully published ownership prepared before the sole CUDA enqueue.
struct PreparedMainTailLaunch {
    desc: MainTailDesc,
    final_level: ContinuationPublishedLevel,
    scratch: DeviceAllocation<E4>,
    program_blob: MainTailProgramBlob,
    entry_keepalive: ContinuationPublishedLevel,
}

/// Launched ownership. The final buffer remains canonical and dense; the
/// other ping-pong buffer remains available as a keepalive.
pub(crate) struct MainTailLaunched {
    final_level: ContinuationPublishedLevel,
    _scratch: DeviceAllocation<E4>,
}

impl MainTailLaunched {
    pub(crate) fn final_level(&self) -> &ContinuationPublishedLevel {
        &self.final_level
    }
}

fn checked_geometry(tail_start: usize, folding_steps: usize) -> (usize, usize) {
    let tail_rounds = folding_steps
        .checked_sub(tail_start)
        .expect("tail start must not exceed the folding steps");
    assert!((1..=6).contains(&tail_rounds));
    assert!(tail_start >= 3);
    assert!(folding_steps <= u8::MAX as usize);
    let entry_column_elems = 8usize
        .checked_shl(tail_rounds as u32)
        .expect("tail geometry must fit usize");
    (tail_rounds, entry_column_elems)
}

fn validate_program(program: &MainTailProgram) {
    assert!(program.list_offsets.len() <= MAIN_TAIL_LIST_OFFSETS);
    assert!(program.program_words.len() <= MAIN_TAIL_PROGRAM_WORD_CAPACITY);
    assert!(program.immediates.len() <= MAIN_TAIL_IMMEDIATE_CAPACITY);
    assert!(usize::from(program.source_count) <= MAIN_TAIL_SOURCE_CAPACITY);
    assert_eq!(
        usize::from(program.list_offsets[MAIN_TAIL_K]),
        program.program_words.len()
    );
    assert!(program.program_words.len().is_multiple_of(3));
    assert_ne!(program.source_count, 0);
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn bind_main_tail(
    expected_layer: usize,
    program: &MainTailProgram,
    entry: ContinuationPublishedLevel,
    tail_start: usize,
    folding_steps: usize,
    eq_boundary: MainEqBoundaryWitness,
    runtime: MainTailRuntimeState,
    context: &ProverContext,
) -> CudaResult<MainTailLaunch> {
    validate_program(program);
    assert_eq!(program.layer, expected_layer);
    let (tail_rounds, entry_column_elems) = checked_geometry(tail_start, folding_steps);
    let final_shape = ContinuationPublishedShape {
        depth: (folding_steps - 1) as u8,
        columns: usize::from(program.source_count),
        column_elems: 2,
    };
    let ping_pong_elems = usize::from(program.source_count)
        .checked_mul(entry_column_elems >> 3)
        .expect("tail allocation size must fit usize");
    let final_elems = final_shape
        .columns
        .checked_mul(final_shape.column_elems)
        .expect("final allocation size must fit usize");
    assert!(final_elems <= ping_pong_elems);
    let expected_shape = ContinuationPublishedShape {
        depth: (tail_start - 3) as u8,
        columns: usize::from(program.source_count),
        column_elems: entry_column_elems,
    };
    assert_eq!(entry.shape(), expected_shape);
    assert_eq!(eq_boundary.consumer_round, tail_start as u8);
    assert_eq!(eq_boundary.semantic_suffix_offset, tail_start as u8 + 1);
    let expected_eq_sizes = make_eq_sizes(tail_rounds - 1);
    assert_eq!(eq_boundary.eq_sizes, expected_eq_sizes);
    assert_eq!(eq_boundary.eq_sizes.high, [0, 0]);
    assert_eq!(eq_boundary.eq_sizes.low, (tail_rounds - 1) as u32);
    for pointer in [
        runtime.eq_low.cast_const().cast::<u8>(),
        runtime.prev_claim_coordinates.cast::<u8>(),
        runtime.seed.cast_const().cast::<u8>(),
        runtime.claim.cast_const().cast::<u8>(),
        runtime.eq_prefactor.cast_const().cast::<u8>(),
        runtime.coefficients_out.cast_const().cast::<u8>(),
        runtime.challenges_out.cast_const().cast::<u8>(),
    ] {
        assert!(!pointer.is_null());
    }

    let mut ping = context.alloc(ping_pong_elems, AllocationPlacement::BestFit)?;
    let mut pong = context.alloc(ping_pong_elems, AllocationPlacement::BestFit)?;

    let program_blob = MainTailProgramBlob {
        bytes: serialize_main_tail_program_blob(program),
    };
    debug_assert!(program_blob.bytes
        [MAIN_TAIL_PROGRAM_OFFSET + program.program_words.len() * 2..MAIN_TAIL_IMMEDIATE_OFFSET]
        .iter()
        .all(|&byte| byte == 0));
    debug_assert!(
        program_blob.bytes[MAIN_TAIL_IMMEDIATE_OFFSET + program.immediates.len() * 4..]
            .iter()
            .all(|&byte| byte == 0)
    );

    let desc = MainTailDesc {
        program_blob: core::ptr::null(),
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
        tail_padding: [0; 14],
    };
    Ok(MainTailLaunch {
        desc,
        tail_rounds,
        final_shape,
        ping_pong_elems,
        final_elems,
        program_blob,
        ping,
        pong,
        entry_keepalive: entry,
    })
}

fn prepare_main_tail_launch(launch: MainTailLaunch) -> PreparedMainTailLaunch {
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
        ContinuationPublishedLevel::try_new(launch.final_shape, final_allocation, publication)
            .expect("main-tail publication must be canonical");
    PreparedMainTailLaunch {
        desc: launch.desc,
        final_level,
        scratch,
        program_blob: launch.program_blob,
        entry_keepalive: launch.entry_keepalive,
    }
}

fn enqueue_prepared_main_tail(
    prepared: PreparedMainTailLaunch,
    context: &ProverContext,
) -> CudaResult<MainTailLaunched> {
    let config = CudaLaunchConfig::basic(1, MAIN_TAIL_BLOCK_THREADS, context.get_exec_stream());
    GkrBwdMainTailFunction::default().launch(
        &config,
        &GkrBwdMainTailArguments::new(prepared.desc, prepared.program_blob),
    )?;
    // The kernel reading the entry has been enqueued; the stream-ordered pool
    // makes releasing its owner safe from here.
    drop(prepared.entry_keepalive);
    Ok(MainTailLaunched {
        final_level: prepared.final_level,
        _scratch: prepared.scratch,
    })
}

/// Prepare exact publication ownership, enqueue the sole kernel, and return it.
pub(crate) fn launch_main_tail(
    launch: MainTailLaunch,
    context: &ProverContext,
) -> CudaResult<MainTailLaunched> {
    let prepared = prepare_main_tail_launch(launch);
    enqueue_prepared_main_tail(prepared, context)
}
