use core::mem::{align_of, offset_of, size_of};

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_gkr_compiler::main_tail::{MAIN_TAIL_K, MAIN_TAIL_LIST_OFFSETS};
use gpu_gkr_compiler::{
    MainTailProgram, KERNEL_ARGUMENT_CEILING_BYTES, LEAN_CLASS_SHIFT, LEAN_CONT_GROUP_HEADER_CLASS,
    LEAN_WORDS_PER_TERM,
};
use gpu_prover_context::ProverContext;

use crate::backward::main_continuation::ContinuationPublishedShape;
use crate::backward::main_layer::execution_plan::MainEqBoundaryWitness;
use crate::backward::{make_eq_sizes, GkrEqSizes};
use crate::proth120::backward::main_continuation::{
    ContinuationPublishedLevelPr, PR_MAIN_FINAL_EVALUATIONS_PER_ADDRESS,
};
use crate::upstream::PR;

pub(crate) const PR_MAIN_TAIL_BLOCK_THREADS: u32 = 256;
pub(crate) const PR_MAIN_TAIL_PROGRAM_OFFSET: usize = MAIN_TAIL_LIST_OFFSETS * size_of::<u16>();
pub(crate) const PR_MAIN_TAIL_PROGRAM_WORD_CAPACITY: usize = 8_192;
pub(crate) const PR_MAIN_TAIL_BLOB_BYTES: usize = (PR_MAIN_TAIL_PROGRAM_OFFSET
    + PR_MAIN_TAIL_PROGRAM_WORD_CAPACITY * size_of::<u16>())
.next_multiple_of(16);
pub(crate) const PR_MAIN_TAIL_IMMEDIATE_CAPACITY: usize = 512;
pub(crate) const PR_MAIN_TAIL_SOURCE_CAPACITY: usize = 1_072;
pub(crate) const PR_MAIN_TAIL_DESCRIPTOR_BYTES: usize = 144;
pub(crate) const PR_MAIN_TAIL_KERNEL_ARGUMENT_BYTES: usize =
    PR_MAIN_TAIL_DESCRIPTOR_BYTES + PR_MAIN_TAIL_BLOB_BYTES;
const PR_MAIN_TAIL_C_INIT_NONE: u16 = u16::MAX;
const CONTINUATION_ID_MASK: u16 = (1 << LEAN_CLASS_SHIFT) - 1;
const PROGRAM_IMMEDIATE_RESERVED: usize = 2;

#[repr(C, align(16))]
#[derive(Clone, Copy, Debug)]
pub(crate) struct MainTailDescPr {
    pub(crate) program_blob: *const u8,
    pub(crate) entry: *const PR,
    pub(crate) ping: *mut PR,
    pub(crate) pong: *mut PR,
    pub(crate) eq_low: *mut PR,
    pub(crate) eq_high: *const PR,
    pub(crate) prev_claim_coordinates: *const PR,
    pub(crate) seed: *mut u8,
    pub(crate) claim: *mut PR,
    pub(crate) eq_prefactor: *mut PR,
    pub(crate) coefficients_out: *mut PR,
    pub(crate) challenges_out: *mut PR,
    pub(crate) coefficients: *const PR,
    pub(crate) immediates: *const PR,
    pub(crate) eq_sizes: GkrEqSizes,
    pub(crate) entry_column_elems: u32,
    pub(crate) source_count: u16,
    pub(crate) program_words: u16,
    pub(crate) immediate_count: u16,
    pub(crate) c_init_coeff_id: u16,
    pub(crate) tail_start: u8,
    pub(crate) folding_steps: u8,
    pub(crate) tail_padding: [u8; 6],
}

#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub(crate) struct MainTailProgramBlobPr {
    pub(crate) bytes: [u8; PR_MAIN_TAIL_BLOB_BYTES],
}

const _: () = {
    assert!(MAIN_TAIL_K == 8);
    assert!(PR_MAIN_TAIL_PROGRAM_OFFSET == 18);
    assert!(PR_MAIN_TAIL_BLOB_BYTES == 16_416);
    assert!(LEAN_WORDS_PER_TERM == 3);
    assert!(size_of::<MainTailDescPr>() == PR_MAIN_TAIL_DESCRIPTOR_BYTES);
    assert!(align_of::<MainTailDescPr>() == 16);
    assert!(offset_of!(MainTailDescPr, program_blob) == 0);
    assert!(offset_of!(MainTailDescPr, entry) == 8);
    assert!(offset_of!(MainTailDescPr, ping) == 16);
    assert!(offset_of!(MainTailDescPr, pong) == 24);
    assert!(offset_of!(MainTailDescPr, eq_low) == 32);
    assert!(offset_of!(MainTailDescPr, eq_high) == 40);
    assert!(offset_of!(MainTailDescPr, prev_claim_coordinates) == 48);
    assert!(offset_of!(MainTailDescPr, seed) == 56);
    assert!(offset_of!(MainTailDescPr, claim) == 64);
    assert!(offset_of!(MainTailDescPr, eq_prefactor) == 72);
    assert!(offset_of!(MainTailDescPr, coefficients_out) == 80);
    assert!(offset_of!(MainTailDescPr, challenges_out) == 88);
    assert!(offset_of!(MainTailDescPr, coefficients) == 96);
    assert!(offset_of!(MainTailDescPr, immediates) == 104);
    assert!(offset_of!(MainTailDescPr, eq_sizes) == 112);
    assert!(offset_of!(MainTailDescPr, entry_column_elems) == 124);
    assert!(offset_of!(MainTailDescPr, source_count) == 128);
    assert!(offset_of!(MainTailDescPr, program_words) == 130);
    assert!(offset_of!(MainTailDescPr, immediate_count) == 132);
    assert!(offset_of!(MainTailDescPr, c_init_coeff_id) == 134);
    assert!(offset_of!(MainTailDescPr, tail_start) == 136);
    assert!(offset_of!(MainTailDescPr, folding_steps) == 137);
    assert!(offset_of!(MainTailDescPr, tail_padding) == 138);
    assert!(size_of::<MainTailProgramBlobPr>() == PR_MAIN_TAIL_BLOB_BYTES);
    assert!(align_of::<MainTailProgramBlobPr>() == 16);
    assert!(PR_MAIN_TAIL_KERNEL_ARGUMENT_BYTES == 16_560);
    assert!(PR_MAIN_TAIL_KERNEL_ARGUMENT_BYTES <= KERNEL_ARGUMENT_CEILING_BYTES);
};

cuda_kernel!(
    PrGkrMainTail,
    ab_pr_gkr_main_tail_kernel(desc: MainTailDescPr, program_blob: MainTailProgramBlobPr)
);

#[derive(Clone, Copy, Debug)]
pub(crate) struct MainTailRuntimePr {
    pub(crate) eq_low: *mut PR,
    pub(crate) eq_high: *const PR,
    pub(crate) prev_claim_coordinates: *const PR,
    pub(crate) seed: *mut u8,
    pub(crate) claim: *mut PR,
    pub(crate) eq_prefactor: *mut PR,
    pub(crate) coefficients_out: *mut PR,
    pub(crate) challenges_out: *mut PR,
    pub(crate) coefficients: *const PR,
    pub(crate) coefficient_count: usize,
    pub(crate) immediates: *const PR,
    pub(crate) immediate_count: usize,
}

pub(crate) struct MainTailLaunchPr {
    desc: MainTailDescPr,
    tail_rounds: usize,
    final_shape: ContinuationPublishedShape,
    program_blob: Box<MainTailProgramBlobPr>,
    ping: DeviceAllocation<PR>,
    pong: DeviceAllocation<PR>,
    entry_keepalive: ContinuationPublishedLevelPr,
}

pub(crate) struct MainTailLaunchedPr {
    final_level: ContinuationPublishedLevelPr,
    _scratch: DeviceAllocation<PR>,
}

impl MainTailLaunchedPr {
    pub(crate) fn final_level(&self) -> &ContinuationPublishedLevelPr {
        &self.final_level
    }
}

fn checked_geometry(tail_start: usize, folding_steps: usize) -> (usize, usize) {
    let tail_rounds = folding_steps
        .checked_sub(tail_start)
        .expect("Proth120 main tail starts after its final round");
    assert!(
        (1..=6).contains(&tail_rounds),
        "Proth120 main tail supports one to six rounds, got {tail_rounds}"
    );
    assert!(
        tail_start >= 3,
        "Proth120 main tail needs a depth-three entry fold"
    );
    assert!(folding_steps <= u8::MAX as usize);
    (tail_rounds, 8usize << tail_rounds)
}

fn validate_program(program: &MainTailProgram, runtime: &MainTailRuntimePr) {
    let words = &program.program_words;
    assert_eq!(program.list_offsets.len(), MAIN_TAIL_LIST_OFFSETS);
    assert!(words.len() <= PR_MAIN_TAIL_PROGRAM_WORD_CAPACITY);
    assert!(words.len().is_multiple_of(LEAN_WORDS_PER_TERM));
    assert_eq!(usize::from(program.list_offsets[MAIN_TAIL_K]), words.len());
    assert!(program.source_count != 0);
    assert!(usize::from(program.source_count) <= PR_MAIN_TAIL_SOURCE_CAPACITY);
    assert!(program.immediates.len() <= PR_MAIN_TAIL_IMMEDIATE_CAPACITY);
    assert_eq!(
        program.immediates.len(),
        runtime.immediate_count,
        "Proth120 main tail immediate table length mismatch"
    );
    let check_coefficient = |id: usize| {
        assert!(
            id < runtime.coefficient_count,
            "Proth120 main tail coefficient {id} exceeds bank length {}",
            runtime.coefficient_count
        );
    };
    if program.c_init_coeff_id != PR_MAIN_TAIL_C_INIT_NONE {
        check_coefficient(usize::from(program.c_init_coeff_id));
    }
    let id = |word: u16| usize::from(word & CONTINUATION_ID_MASK);
    let mut pc = 0;
    while pc < words.len() {
        let header = words[pc];
        check_coefficient(id(header));
        if header >> LEAN_CLASS_SHIFT == LEAN_CONT_GROUP_HEADER_CLASS {
            for _ in 0..words[pc + 1] {
                pc += LEAN_WORDS_PER_TERM;
                let immediate = id(words[pc]);
                assert!(
                    immediate < PROGRAM_IMMEDIATE_RESERVED
                        || immediate - PROGRAM_IMMEDIATE_RESERVED < runtime.immediate_count,
                    "Proth120 main tail immediate {immediate} exceeds table length {}",
                    runtime.immediate_count
                );
            }
        }
        pc += LEAN_WORDS_PER_TERM;
    }
}

pub(crate) fn serialize_main_tail_program_blob_pr(
    program: &MainTailProgram,
) -> Box<MainTailProgramBlobPr> {
    let mut blob = Box::new(MainTailProgramBlobPr {
        bytes: [0u8; PR_MAIN_TAIL_BLOB_BYTES],
    });
    for (index, &offset) in program.list_offsets.iter().enumerate() {
        let at = index * size_of::<u16>();
        blob.bytes[at..at + size_of::<u16>()].copy_from_slice(&offset.to_le_bytes());
    }
    for (index, &word) in program.program_words.iter().enumerate() {
        let at = PR_MAIN_TAIL_PROGRAM_OFFSET + index * size_of::<u16>();
        blob.bytes[at..at + size_of::<u16>()].copy_from_slice(&word.to_le_bytes());
    }
    blob
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn bind_main_tail_pr(
    expected_layer: usize,
    program: &MainTailProgram,
    entry: ContinuationPublishedLevelPr,
    tail_start: usize,
    folding_steps: usize,
    eq_boundary: MainEqBoundaryWitness,
    runtime: MainTailRuntimePr,
    context: &ProverContext,
) -> CudaResult<MainTailLaunchPr> {
    assert_eq!(
        program.layer, expected_layer,
        "Proth120 main tail program belongs to another layer"
    );
    validate_program(program, &runtime);
    let (tail_rounds, entry_column_elems) = checked_geometry(tail_start, folding_steps);
    let columns = usize::from(program.source_count);
    assert_eq!(
        entry.shape(),
        ContinuationPublishedShape {
            depth: (tail_start - 3) as u8,
            columns,
            column_elems: entry_column_elems,
        },
        "Proth120 main tail entry shape mismatch"
    );
    assert_eq!(eq_boundary.consumer_round, tail_start as u8);
    assert_eq!(eq_boundary.semantic_suffix_offset, tail_start as u8 + 1);
    assert_eq!(eq_boundary.eq_sizes, make_eq_sizes(tail_rounds - 1));
    assert_eq!(eq_boundary.eq_sizes.high, [0, 0]);
    for (name, pointer) in [
        ("eq low", runtime.eq_low.cast_const().cast::<u8>()),
        ("eq high", runtime.eq_high.cast::<u8>()),
        (
            "previous claim coordinates",
            runtime.prev_claim_coordinates.cast::<u8>(),
        ),
        ("seed", runtime.seed.cast_const()),
        ("claim", runtime.claim.cast_const().cast::<u8>()),
        (
            "eq prefactor",
            runtime.eq_prefactor.cast_const().cast::<u8>(),
        ),
        (
            "coefficients out",
            runtime.coefficients_out.cast_const().cast::<u8>(),
        ),
        (
            "challenges out",
            runtime.challenges_out.cast_const().cast::<u8>(),
        ),
        ("coefficients", runtime.coefficients.cast::<u8>()),
    ] {
        assert!(
            !pointer.is_null(),
            "Proth120 main tail {name} pointer is null"
        );
    }
    assert!(
        runtime.immediate_count == 0 || !runtime.immediates.is_null(),
        "Proth120 main tail immediates pointer is null"
    );
    let ping_pong_elems = columns
        .checked_mul(entry_column_elems >> 3)
        .expect("Proth120 main tail allocation size overflow");
    let final_shape = ContinuationPublishedShape {
        depth: (folding_steps - 1) as u8,
        columns,
        column_elems: PR_MAIN_FINAL_EVALUATIONS_PER_ADDRESS,
    };
    let mut ping = context.alloc(ping_pong_elems, AllocationPlacement::BestFit)?;
    let mut pong = context.alloc(ping_pong_elems, AllocationPlacement::BestFit)?;
    let desc = MainTailDescPr {
        program_blob: core::ptr::null(),
        entry: entry.as_ptr(),
        ping: ping.as_mut_ptr(),
        pong: pong.as_mut_ptr(),
        eq_low: runtime.eq_low,
        eq_high: runtime.eq_high,
        prev_claim_coordinates: runtime.prev_claim_coordinates,
        seed: runtime.seed,
        claim: runtime.claim,
        eq_prefactor: runtime.eq_prefactor,
        coefficients_out: runtime.coefficients_out,
        challenges_out: runtime.challenges_out,
        coefficients: runtime.coefficients,
        immediates: runtime.immediates,
        eq_sizes: eq_boundary.eq_sizes,
        entry_column_elems: entry_column_elems as u32,
        source_count: program.source_count,
        program_words: program.program_words.len() as u16,
        immediate_count: program.immediates.len() as u16,
        c_init_coeff_id: program.c_init_coeff_id,
        tail_start: tail_start as u8,
        folding_steps: folding_steps as u8,
        tail_padding: [0; 6],
    };
    Ok(MainTailLaunchPr {
        desc,
        tail_rounds,
        final_shape,
        program_blob: serialize_main_tail_program_blob_pr(program),
        ping,
        pong,
        entry_keepalive: entry,
    })
}

pub(crate) fn launch_main_tail_pr(
    launch: MainTailLaunchPr,
    context: &ProverContext,
) -> CudaResult<MainTailLaunchedPr> {
    let (mut final_allocation, scratch) = if launch.tail_rounds % 2 == 1 {
        (launch.ping, launch.pong)
    } else {
        (launch.pong, launch.ping)
    };
    let final_elems = launch.final_shape.columns * launch.final_shape.column_elems;
    assert!(final_elems <= final_allocation.len());
    final_allocation.shrink_len_to(final_elems);
    let final_level = ContinuationPublishedLevelPr::try_new(launch.final_shape, final_allocation)
        .expect("Proth120 main-tail publication must fit its allocation");
    let config = CudaLaunchConfig::basic(1, PR_MAIN_TAIL_BLOCK_THREADS, context.get_exec_stream());
    PrGkrMainTailFunction::default().launch(
        &config,
        &PrGkrMainTailArguments::new(launch.desc, *launch.program_blob),
    )?;
    drop(launch.entry_keepalive);
    Ok(MainTailLaunchedPr {
        final_level,
        _scratch: scratch,
    })
}

#[cfg(test)]
mod cpu_pr_main_tail_abi {
    use super::{MainTailDescPr, PR_MAIN_TAIL_KERNEL_ARGUMENT_BYTES};

    const CUDA_ABI: &str = include_str!("../../../../native/gkr/proth120/backward/main_tail.cuh");

    #[test]
    fn cpu_pr_main_tail_abi_is_exact() {
        assert_eq!(size_of::<MainTailDescPr>(), 144);
        assert_eq!(PR_MAIN_TAIL_KERNEL_ARGUMENT_BYTES, 16_560);
        for (field, offset) in [
            ("entry", 8),
            ("eq_high", 40),
            ("seed", 56),
            ("coefficients", 96),
            ("immediates", 104),
            ("eq_sizes", 112),
            ("entry_column_elems", 124),
            ("source_count", 128),
            ("c_init_coeff_id", 134),
            ("tail_start", 136),
            ("folding_steps", 137),
        ] {
            let assertion =
                format!("__builtin_offsetof(bwd_pr_main_tail_desc, {field}) == {offset}");
            assert!(
                CUDA_ABI.contains(&assertion),
                "missing CUDA assertion {assertion}"
            );
        }
        assert!(CUDA_ABI.contains(
            "sizeof(bwd_pr_main_tail_desc) + sizeof(bwd_pr_main_tail_program_blob) == 16560"
        ));
    }
}
