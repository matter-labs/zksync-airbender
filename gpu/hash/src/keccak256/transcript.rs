use era_cudart::cuda_kernel;
use era_cudart::device::{device_get_attribute, get_device};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_set_async;
use era_cudart::occupancy::max_active_blocks_per_multiprocessor;
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaDeviceAttr;
use gpu_core::primitives::field::PR;

use super::{
    assert_no_overlap, checked_bytes, checked_product, checked_u32, checked_u64, grid_dim,
    BLOCK_THREADS, SEED_BYTES,
};
use crate::pow::pow_chunk_steps;

fn assert_seed(name: &str, seed: &DeviceSlice<u8>) {
    assert_eq!(
        seed.len(),
        SEED_BYTES,
        "keccak256::{name}: seed.len() == 32"
    );
}

fn absorbed_count<T>(name: &str, input: &DeviceSlice<T>, prefix: usize) -> u64 {
    checked_bytes::<T>(name, input.len())
        .checked_add(prefix)
        .unwrap_or_else(|| panic!("keccak256::{name}: count overflow"));
    checked_u64(name, input.len())
}

fn single_thread(stream: &CudaStream) -> CudaLaunchConfig<'_> {
    CudaLaunchConfig::basic(1, 1, stream)
}

cuda_kernel!(
    TranscriptInitialU32,
    ab_keccak256_transcript_initial_u32_kernel(input: *const u32, count: u64, seed_out: *mut u8)
);

cuda_kernel!(
    TranscriptCommitU32,
    ab_keccak256_transcript_commit_u32_kernel(seed_io: *mut u8, input: *const u32, count: u64)
);

cuda_kernel!(
    TranscriptCommitFields,
    ab_keccak256_transcript_commit_fields_kernel(seed_io: *mut u8, input: *const PR, count: u64)
);

cuda_kernel!(
    TranscriptDrawU32,
    ab_keccak256_transcript_draw_u32_kernel(seed_io: *mut u8, out: *mut u32, count: u64)
);

cuda_kernel!(
    TranscriptDrawFields,
    ab_keccak256_transcript_draw_fields_kernel(seed_io: *mut u8, out: *mut PR, count: u64)
);

pub fn transcript_commit_initial_u32(
    input: &DeviceSlice<u32>,
    seed: &mut DeviceSlice<u8>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "transcript_commit_initial_u32";
    assert_seed(NAME, seed);
    let count = absorbed_count(NAME, input, 0);
    assert_no_overlap(NAME, input, seed);
    let args = TranscriptInitialU32Arguments::new(input.as_ptr(), count, seed.as_mut_ptr());
    TranscriptInitialU32Function::default().launch(&single_thread(stream), &args)
}

pub fn transcript_commit_u32(
    seed: &mut DeviceSlice<u8>,
    input: &DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "transcript_commit_u32";
    assert_seed(NAME, seed);
    let count = absorbed_count(NAME, input, SEED_BYTES);
    assert_no_overlap(NAME, input, seed);
    let args = TranscriptCommitU32Arguments::new(seed.as_mut_ptr(), input.as_ptr(), count);
    TranscriptCommitU32Function::default().launch(&single_thread(stream), &args)
}

pub fn transcript_commit_fields(
    seed: &mut DeviceSlice<u8>,
    input: &DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "transcript_commit_fields";
    assert_seed(NAME, seed);
    let count = absorbed_count(NAME, input, SEED_BYTES);
    assert_no_overlap(NAME, input, seed);
    let args = TranscriptCommitFieldsArguments::new(seed.as_mut_ptr(), input.as_ptr(), count);
    TranscriptCommitFieldsFunction::default().launch(&single_thread(stream), &args)
}

pub fn transcript_draw_u32(
    seed: &mut DeviceSlice<u8>,
    out: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "transcript_draw_u32";
    assert_seed(NAME, seed);
    let count = absorbed_count(NAME, out, 0);
    assert_no_overlap(NAME, out, seed);
    if count == 0 {
        return Ok(());
    }
    let args = TranscriptDrawU32Arguments::new(seed.as_mut_ptr(), out.as_mut_ptr(), count);
    TranscriptDrawU32Function::default().launch(&single_thread(stream), &args)
}

pub fn transcript_draw_fields(
    seed: &mut DeviceSlice<u8>,
    out: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "transcript_draw_fields";
    assert_seed(NAME, seed);
    let count = absorbed_count(NAME, out, 0);
    assert_no_overlap(NAME, out, seed);
    if count == 0 {
        return Ok(());
    }
    let args = TranscriptDrawFieldsArguments::new(seed.as_mut_ptr(), out.as_mut_ptr(), count);
    TranscriptDrawFieldsFunction::default().launch(&single_thread(stream), &args)
}

cuda_kernel!(
    Keccak256Pow,
    ab_keccak256_pow_kernel(
        seed: *const u8,
        bits: u32,
        max_nonce: u64,
        chunk_steps: u32,
        counter: *mut u64,
        result: *mut u64
    )
);

cuda_kernel!(
    Keccak256PowFinalize,
    ab_keccak256_pow_finalize_kernel(seed_io: *mut u8, bits: u32, nonce: *const u64)
);

cuda_kernel!(
    Keccak256PowHelpersProbe,
    ab_keccak256_pow_helpers_probe_kernel(
        digests: *const u8,
        bits: *const u32,
        candidates: *const u64,
        strides: *const u64,
        count: u64,
        predicates: *mut u32,
        next: *mut u64,
        can_advance: *mut u32
    )
);

fn pow_shape(name: &str, seed: &DeviceSlice<u8>, bits: u32, nonce: &DeviceVariable<u64>) {
    assert_seed(name, seed);
    assert!(bits <= 256, "keccak256::{name}: bits <= 256");
    assert_no_overlap(name, seed, nonce);
}

fn pow_grid(name: &str, max_nonce: u64, blocks: u32) {
    assert!(blocks > 0, "keccak256::{name}: blocks > 0");
    assert!(
        blocks <= i32::MAX as u32,
        "keccak256::{name}: grid <= 2^31 - 1"
    );
    let stride = checked_u64(
        name,
        checked_product(name, blocks as usize, BLOCK_THREADS as usize),
    );
    assert!(
        stride <= max_nonce,
        "keccak256::{name}: stride <= max_nonce"
    );
}

pub(super) fn pow_finalize(
    seed: &mut DeviceSlice<u8>,
    bits: u32,
    nonce: &DeviceVariable<u64>,
    stream: &CudaStream,
) -> CudaResult<()> {
    pow_shape("pow_finalize", seed, bits, nonce);
    let args = Keccak256PowFinalizeArguments::new(seed.as_mut_ptr(), bits, nonce.as_ptr());
    Keccak256PowFinalizeFunction::default().launch(&single_thread(stream), &args)
}

/// Writes the minimum valid nonce in every build; `counter` is one-word scratch.
pub fn keccak256_pow(
    seed: &mut DeviceSlice<u8>,
    bits: u32,
    nonce: &mut DeviceVariable<u64>,
    counter: &mut DeviceVariable<u64>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "keccak256_pow";
    pow_shape(NAME, seed, bits, nonce);
    assert_no_overlap(NAME, nonce, counter);
    assert_no_overlap(NAME, seed, counter);
    if bits == 0 {
        unsafe {
            memory_set_async(nonce.transmute_mut(), 0, stream)?;
        }
    } else {
        let device = get_device()?;
        let mpc = device_get_attribute(CudaDeviceAttr::MultiProcessorCount, device)?;
        let kernel = Keccak256PowFunction::default();
        let active = max_active_blocks_per_multiprocessor(&kernel, BLOCK_THREADS as i32, 0)?;
        assert!(active > 0, "keccak256::{NAME}: occupancy > 0");
        assert!(mpc > 0, "keccak256::{NAME}: multiprocessor count > 0");
        let blocks = checked_u32(NAME, checked_product(NAME, mpc as usize, active as usize));
        pow_grid(NAME, u64::MAX, blocks);
        unsafe {
            memory_set_async(nonce.transmute_mut(), 0xff, stream)?;
            memory_set_async(counter.transmute_mut(), 0, stream)?;
        }
        let args = Keccak256PowArguments::new(
            seed.as_ptr(),
            bits,
            u64::MAX,
            pow_chunk_steps(bits, blocks),
            counter.as_mut_ptr(),
            nonce.as_mut_ptr(),
        );
        kernel.launch(
            &CudaLaunchConfig::basic(blocks, BLOCK_THREADS, stream),
            &args,
        )?;
    }
    pow_finalize(seed, bits, nonce, stream)
}

#[cfg(test)]
pub(super) fn pow_search_bounded(
    seed: &DeviceSlice<u8>,
    bits: u32,
    max_nonce: u64,
    blocks: u32,
    first_chunk: u64,
    nonce: &mut DeviceVariable<u64>,
    counter: &mut DeviceVariable<u64>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "pow_search_bounded";
    pow_shape(NAME, seed, bits, nonce);
    assert_no_overlap(NAME, nonce, counter);
    pow_grid(NAME, max_nonce, blocks);
    unsafe {
        memory_set_async(nonce.transmute_mut(), 0xff, stream)?;
    }
    era_cudart::memory::memory_copy_async(counter, std::slice::from_ref(&first_chunk), stream)?;
    let args = Keccak256PowArguments::new(
        seed.as_ptr(),
        bits,
        max_nonce,
        pow_chunk_steps(bits, blocks),
        counter.as_mut_ptr(),
        nonce.as_mut_ptr(),
    );
    Keccak256PowFunction::default().launch(
        &CudaLaunchConfig::basic(blocks, BLOCK_THREADS, stream),
        &args,
    )
}

#[doc(hidden)]
pub fn pow_helpers_probe(
    digests: &DeviceSlice<u8>,
    bits: &DeviceSlice<u32>,
    candidates: &DeviceSlice<u64>,
    strides: &DeviceSlice<u64>,
    predicates: &mut DeviceSlice<u32>,
    next: &mut DeviceSlice<u64>,
    can_advance: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    const NAME: &str = "pow_helpers_probe";
    let count = bits.len();
    assert_eq!(
        digests.len(),
        checked_product(NAME, count, SEED_BYTES),
        "keccak256::{NAME}: digests.len() == 32 * count"
    );
    assert_eq!(
        candidates.len(),
        count,
        "keccak256::{NAME}: candidates.len() == count"
    );
    assert_eq!(
        strides.len(),
        count,
        "keccak256::{NAME}: strides.len() == count"
    );
    assert_eq!(
        predicates.len(),
        count,
        "keccak256::{NAME}: predicates.len() == count"
    );
    assert_eq!(next.len(), count, "keccak256::{NAME}: next.len() == count");
    assert_eq!(
        can_advance.len(),
        count,
        "keccak256::{NAME}: can_advance.len() == count"
    );
    for out in [&*predicates, &*can_advance] {
        assert_no_overlap(NAME, out, digests);
        assert_no_overlap(NAME, out, bits);
        assert_no_overlap(NAME, out, candidates);
        assert_no_overlap(NAME, out, strides);
        assert_no_overlap(NAME, out, next);
    }
    assert_no_overlap(NAME, predicates, can_advance);
    assert_no_overlap(NAME, next, digests);
    assert_no_overlap(NAME, next, bits);
    assert_no_overlap(NAME, next, candidates);
    assert_no_overlap(NAME, next, strides);
    let blocks = grid_dim(NAME, count, BLOCK_THREADS);
    let count = checked_u64(NAME, count);
    if count == 0 {
        return Ok(());
    }
    let args = Keccak256PowHelpersProbeArguments::new(
        digests.as_ptr(),
        bits.as_ptr(),
        candidates.as_ptr(),
        strides.as_ptr(),
        count,
        predicates.as_mut_ptr(),
        next.as_mut_ptr(),
        can_advance.as_mut_ptr(),
    );
    Keccak256PowHelpersProbeFunction::default().launch(
        &CudaLaunchConfig::basic(blocks, BLOCK_THREADS, stream),
        &args,
    )
}
