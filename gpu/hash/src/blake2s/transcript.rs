use era_cudart::cuda_kernel;
use era_cudart::device::{device_get_attribute, get_device};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_set_async;
use era_cudart::occupancy::max_active_blocks_per_multiprocessor;
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaDeviceAttr;

use super::STATE_SIZE;
use gpu_core::primitives::field::E4;
use gpu_core::primitives::utils::WARP_SIZE;

cuda_kernel!(Blake2SPow, ab_blake2s_pow_kernel(seed: *const u32, bits_count: u32, max_nonce: u64, result: *mut u64));

cuda_kernel!(
    pub(crate) TranscriptCommitInitial,
    ab_transcript_commit_initial_kernel(seed_out: *mut u32, input: *const u32, input_len: u32)
);

/// Maximum number of input chunks the chunked transcript-commit kernel-arg
/// descriptor can hold. The pre-WHIR transcript pack feeds 5 chunks
/// (canonical-top-bits + external_challenges + setup cap + memory cap +
/// witness cap); 8 leaves headroom without any meaningful kernel-arg cost.
pub const GKR_CHUNKED_COMMIT_MAX_CHUNKS: usize = 8;

/// Kernel-arg descriptor for `transcript_commit_initial_chunked`. Streams
/// Blake2s over the logical concatenation of `num_chunks` device-resident
/// u32 buffers in one kernel launch (no host-side concat staging).
#[repr(C)]
#[derive(Clone, Copy)]
pub struct GpuChunkedInputDesc {
    /// Number of populated entries in `src_ptrs` and `chunk_lens`.
    pub num_chunks: u32,
    /// Padding to keep the `u64` array 8-byte aligned across language
    /// boundaries.
    pub _pad: u32,
    /// Source device pointers (one per chunk). Each is treated as a
    /// `const u32 *` of length `chunk_lens[i]`.
    pub src_ptrs: [u64; GKR_CHUNKED_COMMIT_MAX_CHUNKS],
    /// Per-chunk u32 word counts.
    pub chunk_lens: [u32; GKR_CHUNKED_COMMIT_MAX_CHUNKS],
}

impl Default for GpuChunkedInputDesc {
    fn default() -> Self {
        Self {
            num_chunks: 0,
            _pad: 0,
            src_ptrs: [0u64; GKR_CHUNKED_COMMIT_MAX_CHUNKS],
            chunk_lens: [0u32; GKR_CHUNKED_COMMIT_MAX_CHUNKS],
        }
    }
}

const _: () = {
    assert!(
        std::mem::size_of::<GpuChunkedInputDesc>() <= 32 * 1024,
        "GpuChunkedInputDesc must fit under the 32 KB inline kernel-arg ceiling"
    );
};

cuda_kernel!(
    TranscriptCommitInitialChunked,
    ab_transcript_commit_initial_chunked_kernel(desc: GpuChunkedInputDesc, seed_out: *mut u32)
);

cuda_kernel!(
    TranscriptCommit,
    ab_transcript_commit_kernel(seed_io: *mut u32, input: *const u32, input_len: u32)
);

cuda_kernel!(
    TranscriptSqueeze,
    ab_transcript_squeeze_kernel(seed_io: *mut u32, output: *mut u32, output_len: u32)
);

cuda_kernel!(
    TranscriptSqueezeE4,
    ab_transcript_squeeze_e4_kernel(seed_io: *mut u32, output_e4: *mut E4, count: u32)
);

/// Chunked variant of [`transcript_commit_initial`]: computes
/// `seed = Blake2s(chunk_0 || chunk_1 || ... || chunk_{N-1})` from the IV without
/// requiring the host to first concatenate the chunks into a single contiguous
/// device buffer. `seed` must be exactly `STATE_SIZE` u32 words; written.
/// `chunks` are `(device pointer, u32 length)` pairs covering the logical
/// transcript prefix in order. Producing the same digest as the single-buffer
/// kernel is covered by `transcript_commit_initial_chunked_parity_*`.
pub fn transcript_commit_initial_chunked(
    seed: &mut DeviceSlice<u32>,
    chunks: &[(*const u32, u32)],
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(seed.len(), STATE_SIZE);
    let num_chunks = chunks.len();
    assert!(
        num_chunks <= GKR_CHUNKED_COMMIT_MAX_CHUNKS,
        "transcript_commit_initial_chunked: {num_chunks} chunks exceeds GKR_CHUNKED_COMMIT_MAX_CHUNKS = {GKR_CHUNKED_COMMIT_MAX_CHUNKS}",
    );
    let mut desc = GpuChunkedInputDesc::default();
    desc.num_chunks = num_chunks as u32;
    for (i, (ptr, len)) in chunks.iter().enumerate() {
        desc.src_ptrs[i] = *ptr as u64;
        desc.chunk_lens[i] = *len;
    }
    let seed_ptr = seed.as_mut_ptr();
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = TranscriptCommitInitialChunkedArguments::new(desc, seed_ptr);
    TranscriptCommitInitialChunkedFunction::default().launch(&config, &args)
}

/// Device-side `commit_with_seed`: computes `new_seed = Blake2s(old_seed || input)`.
///
/// `seed` must be exactly `STATE_SIZE` u32 words. Updated in place.
/// `input` contains the field-element data to absorb.
pub fn transcript_commit(
    seed: &mut DeviceSlice<u32>,
    input: &DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(seed.len(), STATE_SIZE);
    let seed_ptr = seed.as_mut_ptr();
    let input_ptr = input.as_ptr();
    let input_len = input.len() as u32;
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = TranscriptCommitArguments::new(seed_ptr, input_ptr, input_len);
    TranscriptCommitFunction::default().launch(&config, &args)
}

/// Device-side `draw_randomness`: expands the seed into `output.len()` u32 words.
///
/// The first `STATE_SIZE` words of `output` are the seed itself (no hashing).
/// If more than `STATE_SIZE` words are requested, additional chunks are produced
/// by iteratively hashing the seed. `seed` is updated in place when
/// `output.len() > STATE_SIZE`.
///
/// `output.len()` must be a positive multiple of `STATE_SIZE`.
pub fn transcript_squeeze(
    seed: &mut DeviceSlice<u32>,
    output: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(seed.len(), STATE_SIZE);
    let output_len = output.len();
    assert!(output_len > 0);
    assert_eq!(output_len % STATE_SIZE, 0);
    let seed_ptr = seed.as_mut_ptr();
    let output_ptr = output.as_mut_ptr();
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = TranscriptSqueezeArguments::new(seed_ptr, output_ptr, output_len as u32);
    TranscriptSqueezeFunction::default().launch(&config, &args)
}

/// Device-side `draw_random_field_els::<BF, E4>(seed, count)`. Produces `count` E4 challenges
/// in Montgomery form by squeezing raw u32 words from `seed` and applying per-limb
/// `from_raw_repr_with_reduction`. `seed` is updated in place to the post-draw state.
pub fn transcript_squeeze_e4(
    seed: &mut DeviceSlice<u32>,
    output: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(seed.len(), STATE_SIZE);
    let count = output.len();
    assert!(count > 0);
    assert!(count <= u32::MAX as usize);
    let seed_ptr = seed.as_mut_ptr();
    let output_ptr = output.as_mut_ptr();
    let config = CudaLaunchConfig::basic(1u32, 1u32, stream);
    let args = TranscriptSqueezeE4Arguments::new(seed_ptr, output_ptr, count as u32);
    TranscriptSqueezeE4Function::default().launch(&config, &args)
}

pub fn blake2s_pow(
    seed: &DeviceSlice<u32>,
    bits_count: u32,
    max_nonce: u64,
    result: &mut DeviceVariable<u64>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(seed.len(), STATE_SIZE);
    unsafe {
        memory_set_async(result.transmute_mut(), 0xff, stream)?;
    }
    const BLOCK_SIZE: u32 = WARP_SIZE * 4;
    let device_id = get_device()?;
    let mpc = device_get_attribute(CudaDeviceAttr::MultiProcessorCount, device_id)?;
    let kernel_function = Blake2SPowFunction::default();
    let max_blocks = max_active_blocks_per_multiprocessor(&kernel_function, BLOCK_SIZE as i32, 0)?;
    let num_blocks = (mpc * max_blocks) as u32;
    let config = CudaLaunchConfig::basic(num_blocks, BLOCK_SIZE, stream);
    let seed = seed.as_ptr();
    let result = result.as_mut_ptr();
    let args = Blake2SPowArguments {
        seed,
        bits_count,
        max_nonce,
        result,
    };
    kernel_function.launch(&config, &args)
}
