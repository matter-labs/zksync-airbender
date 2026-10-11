use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use gpu_core::primitives::field::PR;

use super::{assert_no_overlap, checked_bytes, checked_u64, SEED_BYTES};

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
