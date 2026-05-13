use crate::ops::bit_reverse::bit_reverse_in_place;
use crate::primitives::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride, PtrAndStride,
};
use crate::primitives::field::{BF, E4};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, LOG_WARP_SIZE, WARP_SIZE};
use era_cudart::cuda_kernel;
use era_cudart::device::{device_get_attribute, get_device};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_set_async;
use era_cudart::occupancy::max_active_blocks_per_multiprocessor;
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use era_cudart_sys::CudaDeviceAttr;

pub(crate) const STATE_SIZE: usize = 8;

pub(crate) type Digest = [u32; STATE_SIZE];

pub(crate) type DG = Digest;

cuda_kernel!(
    Leaves,
    ab_blake2s_leaves_kernel(
        values: *const BF,
        results: *mut DG,
        log_rows_per_hash: u32,
        cols_count: u32,
        count: u32,
    )
);

pub(crate) fn launch_leaves_kernel(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<DG>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let values_len = values.len();
    let count = results.len();
    let values = values.as_ptr();
    let results = results.as_mut_ptr();
    assert_eq!(values_len % (count << log_rows_per_hash), 0);
    let cols_count = values_len / (count << log_rows_per_hash);
    assert!(cols_count <= u32::MAX as usize);
    let cols_count = cols_count as u32;
    assert!(count <= u32::MAX as usize);
    let count = count as u32;
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = LeavesArguments::new(values, results, log_rows_per_hash, cols_count, count);
    LeavesFunction::default().launch(&config, &args)
}

pub(crate) fn build_merkle_tree_leaves(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<DG>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let values_len = values.len();
    let leaves_count = results.len();
    assert_eq!(values_len % leaves_count, 0);
    launch_leaves_kernel(values, results, log_rows_per_hash, stream)
}

cuda_kernel!(Nodes, ab_blake2s_nodes_kernel(values: *const DG, results: *mut DG, count: u32,));

pub(crate) fn launch_nodes_kernel(
    values: &DeviceSlice<DG>,
    results: &mut DeviceSlice<DG>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let values_len = values.len();
    let results_len = results.len();
    assert_eq!(values_len, results_len * 2);
    let values = values.as_ptr();
    let results = results.as_mut_ptr();
    assert!(results_len <= u32::MAX as usize);
    let count = results_len as u32;
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = NodesArguments::new(values, results, count);
    NodesFunction::default().launch(&config, &args)
}

pub(crate) fn build_merkle_tree_nodes(
    values: &DeviceSlice<DG>,
    results: &mut DeviceSlice<DG>,
    layers_count: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    if layers_count == 0 {
        Ok(())
    } else {
        let values_len = values.len();
        let results_len = results.len();
        let layer = values_len.trailing_zeros();
        assert_eq!(values_len, 1 << layer);
        assert_eq!(values_len, results_len);
        let (nodes, nodes_remaining) = results.split_at_mut(results_len >> 1);
        launch_nodes_kernel(values, nodes, stream)?;
        build_merkle_tree_nodes(nodes, nodes_remaining, layers_count - 1, stream)
    }
}

pub(crate) fn build_merkle_tree(
    values: &DeviceSlice<BF>,
    results: &mut DeviceSlice<DG>,
    log_rows_per_hash: u32,
    stream: &CudaStream,
    layers_count: u32,
    bit_reverse_leaves: bool,
) -> CudaResult<()> {
    assert_ne!(layers_count, 0);
    let values_len = values.len();
    let results_len = results.len();
    assert_eq!(results_len % 2, 0);
    let leaves_count = results_len / 2;
    assert!(1 << (layers_count - 1) <= leaves_count);
    assert_eq!(values_len % leaves_count, 0);
    let (leaves, nodes) = results.split_at_mut(leaves_count);
    build_merkle_tree_leaves(values, leaves, log_rows_per_hash, stream)?;
    if bit_reverse_leaves {
        bit_reverse_in_place(leaves, stream)?;
    }
    build_merkle_tree_nodes(leaves, nodes, layers_count - 1, stream)
}

cuda_kernel!(
GatherRows,
ab_gather_rows_kernel(
    indexes: *const u32,
    indexes_count: u32,
    bit_reversed_indexes: bool,
    log_rows_count: u32,
    values: PtrAndStride<BF>,
    results: MutPtrAndStride<BF>,
)
);

cuda_kernel!(
    GatherLeafRows,
    ab_gather_leaf_rows_kernel(
        indexes: *const u32,
        indexes_count: u32,
        bit_reversed_indexes: bool,
        log_leaves_count: u32,
        log_rows_per_leaf: u32,
        values: PtrAndStride<BF>,
        results: MutPtrAndStride<BF>,
    )
);

pub(crate) fn gather_leaf_rows(
    indexes: &DeviceSlice<u32>,
    bit_reverse_indexes: bool,
    log_rows_per_leaf: u32,
    values: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    result: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    stream: &CudaStream,
) -> CudaResult<()> {
    let indexes_len = indexes.len();
    let values_cols = values.cols();
    let values_rows = values.rows();
    assert!(values_rows.is_power_of_two());
    let log_rows_count = values_rows.trailing_zeros();
    assert!(log_rows_count >= log_rows_per_leaf);
    let log_leaves_count = log_rows_count - log_rows_per_leaf;
    let result_rows = result.rows();
    let result_cols = result.cols();
    let rows_per_leaf = 1 << log_rows_per_leaf;
    assert_eq!(result_cols, values_cols);
    assert_eq!(result_rows, indexes_len << log_rows_per_leaf);
    assert!(indexes_len <= u32::MAX as usize);
    let indexes_count = indexes_len as u32;
    let (mut grid_dim, block_dim) = if log_rows_per_leaf < LOG_WARP_SIZE {
        get_grid_block_dims_for_threads_count(
            1 << (LOG_WARP_SIZE - log_rows_per_leaf),
            indexes_count,
        )
    } else {
        (indexes_count.into(), 1.into())
    };
    let block_dim = (rows_per_leaf, block_dim.x);
    assert!(result_cols <= u32::MAX as usize);
    grid_dim.y = result_cols as u32;
    let indexes = indexes.as_ptr();
    let values = values.as_ptr_and_stride();
    let result = result.as_mut_ptr_and_stride();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GatherLeafRowsArguments::new(
        indexes,
        indexes_count,
        bit_reverse_indexes,
        log_leaves_count,
        log_rows_per_leaf,
        values,
        result,
    );
    GatherLeafRowsFunction::default().launch(&config, &args)
}

cuda_kernel!(
    GatherMerklePaths,
    ab_gather_merkle_paths_kernel(
        indexes: *const u32,
        indexes_count: u32,
        values: *const DG,
        log_leaves_count: u32,
        results: *mut DG,
    )
);

pub(crate) fn gather_merkle_paths_device(
    indexes: &DeviceSlice<u32>,
    values: &DeviceSlice<DG>,
    results: &mut DeviceSlice<DG>,
    layers_count: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(indexes.len() <= u32::MAX as usize);
    let indexes_count = indexes.len() as u32;
    let values_count = values.len();
    assert!(values_count.is_power_of_two());
    let log_values_count = values_count.trailing_zeros();
    assert_ne!(log_values_count, 0);
    let log_leaves_count = log_values_count - 1;
    // A per-coset cap of size 1 means the query path spans the full coset subtree depth.
    assert!(layers_count <= log_leaves_count);
    assert_eq!(indexes.len() * layers_count as usize, results.len());
    assert_eq!(WARP_SIZE % STATE_SIZE as u32, 0);
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE / STATE_SIZE as u32, indexes_count);
    let grid_dim = (grid_dim.x, layers_count);
    let block_dim = (STATE_SIZE as u32, block_dim.x);
    let indexes = indexes.as_ptr();
    let values = values.as_ptr();
    let result = results.as_mut_ptr();
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args =
        GatherMerklePathsArguments::new(indexes, indexes_count, values, log_leaves_count, result);
    GatherMerklePathsFunction::default().launch(&config, &args)
}

cuda_kernel!(
    GatherRowsAndMerklePaths,
    ab_gather_rows_and_merkle_paths_kernel(
        indexes: *const u32,
        indexes_count: u32,
        bit_reverse_indexes: bool,
        values: *const BF,
        log_rows_per_leaf: u32,
        cols_count: u32,
        log_total_leaves_count: u32,
        leaf_values: MutPtrAndStride<BF>,
        tree_bottom: *const Digest,
        layers_count: u32,
        merkle_paths: *mut Digest,
    )
);

cuda_kernel!(
    GatherMerklePathsFromRows,
    ab_gather_merkle_paths_from_rows_kernel(
        indexes: *const u32,
        indexes_count: u32,
        bit_reverse_indexes: bool,
        values: *const BF,
        log_rows_per_leaf: u32,
        cols_count: u32,
        log_total_leaves_count: u32,
        tree_bottom: *const Digest,
        layers_count: u32,
        merkle_paths: *mut Digest,
    )
);

pub(crate) fn gather_merkle_paths_from_rows(
    indexes: &DeviceSlice<u32>,
    bit_reverse_indexes: bool,
    values: &DeviceSlice<BF>,
    log_rows_per_leaf: u32,
    cols_count: usize,
    tree_bottom: &DeviceSlice<Digest>,
    merkle_paths: &mut DeviceSlice<Digest>,
    layers_count: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let indexes_len = indexes.len();
    let values_len = values.len();
    assert_eq!(values_len % cols_count, 0);
    let log_rows_count = (values_len / cols_count).trailing_zeros();
    assert!(indexes_len <= u32::MAX as usize);
    let indexes_count = indexes_len as u32;
    assert!(layers_count >= LOG_WARP_SIZE);
    assert_eq!(indexes_len * layers_count as usize, merkle_paths.len());
    assert!(cols_count <= u32::MAX as usize);
    let cols_count = cols_count as u32;
    let log_total_leaves_count = log_rows_count as u32 - log_rows_per_leaf;
    let config = CudaLaunchConfig::basic(indexes_count, WARP_SIZE, stream);
    let indexes = indexes.as_ptr();
    let values = values.as_ptr();
    let tree_bottom = tree_bottom.as_ptr();
    let merkle_paths = merkle_paths.as_mut_ptr();
    let args = GatherMerklePathsFromRowsArguments::new(
        indexes,
        indexes_count,
        bit_reverse_indexes,
        values,
        log_rows_per_leaf,
        cols_count,
        log_total_leaves_count,
        tree_bottom,
        layers_count,
        merkle_paths,
    );
    GatherMerklePathsFromRowsFunction::default().launch(&config, &args)
}

pub(crate) fn merkle_tree_cap(
    values: &DeviceSlice<DG>,
    log_tree_cap_size: u32,
) -> &DeviceSlice<DG> {
    let values_len = values.len();
    assert_ne!(values_len, 0);
    assert!(values_len.is_power_of_two());
    let log_values_len = values_len.trailing_zeros();
    assert!(log_values_len > log_tree_cap_size);
    let offset = values_len - (1 << (log_tree_cap_size + 1));
    &values[offset..offset + (1 << log_tree_cap_size)]
}

cuda_kernel!(Blake2SPow, ab_blake2s_pow_kernel(seed: *const u32, bits_count: u32, max_nonce: u64, result: *mut u64));

cuda_kernel!(
    GatherTreeCaps,
    ab_gather_tree_caps_kernel(
        src_ptrs: *const u64,
        dst: *mut u32,
        cap_words_per_coset: u32,
        coset_count: u32
    )
);

/// Maximum coset count the inline `gather_tree_caps_inline` kernel-arg
/// descriptor can hold. Sized for headroom — production lde_factor is
/// typically ≤ 4.
pub(crate) const GKR_GATHER_TREE_CAPS_MAX_COSETS: usize = 32;

/// Kernel-arg descriptor for `gather_tree_caps_inline`. Inline form: the
/// pointer table rides as `__grid_constant__` data, avoiding the
/// runtime-pointer-table H2D `gather_tree_caps` needs.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGatherTreeCapsDesc {
    /// Number of populated entries in `src_ptrs`.
    pub coset_count: u32,
    /// Number of u32 words gathered per source coset.
    pub cap_words_per_coset: u32,
    /// Source device pointers (one per coset). Each is treated as a
    /// `const u32 *` referring to `cap_words_per_coset` u32 words.
    pub src_ptrs: [u64; GKR_GATHER_TREE_CAPS_MAX_COSETS],
}

impl Default for GpuGatherTreeCapsDesc {
    fn default() -> Self {
        Self {
            coset_count: 0,
            cap_words_per_coset: 0,
            src_ptrs: [0u64; GKR_GATHER_TREE_CAPS_MAX_COSETS],
        }
    }
}

const _: () = {
    assert!(
        std::mem::size_of::<GpuGatherTreeCapsDesc>() <= 32 * 1024,
        "GpuGatherTreeCapsDesc must fit under the 32 KB inline kernel-arg ceiling"
    );
};

cuda_kernel!(
    GatherTreeCapsInline,
    ab_gather_tree_caps_inline_kernel(desc: GpuGatherTreeCapsDesc, dst: *mut u32)
);

/// Maximum source addresses the `gather_e_addresses` kernel-arg descriptor
/// can hold. See [`crate::prover::gkr::gkr_address_audit_helpers::GKR_GATHER_MAX_ADDRESSES`]
/// for the rationale; the audit panics if any future circuit exceeds this.
pub(crate) const GKR_GATHER_MAX_ADDRESSES: usize = 1280;

/// Kernel-arg descriptor for `gather_e_addresses`. Inline form: passed by
/// value as `__grid_constant__` data.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuGatherEAddressesDesc {
    /// Number of populated entries in `src_ptrs`.
    pub num_addresses: u32,
    /// Number of E4 elements gathered per source address.
    pub elements_per_addr: u32,
    /// Source device pointers (one per address). Each is treated as a
    /// `const u32 *` referring to `elements_per_addr * 4` u32 words.
    pub src_ptrs: [u64; GKR_GATHER_MAX_ADDRESSES],
}

impl Default for GpuGatherEAddressesDesc {
    fn default() -> Self {
        Self {
            num_addresses: 0,
            elements_per_addr: 0,
            src_ptrs: [0u64; GKR_GATHER_MAX_ADDRESSES],
        }
    }
}

const _: () = {
    assert!(
        std::mem::size_of::<GpuGatherEAddressesDesc>() <= 32 * 1024,
        "GpuGatherEAddressesDesc must fit under the 32 KB inline kernel-arg ceiling"
    );
};

cuda_kernel!(
    GatherEAddresses,
    ab_gather_e_addresses_kernel(desc: GpuGatherEAddressesDesc, dst: *mut u32)
);

cuda_kernel!(
    TranscriptCommitInitial,
    ab_transcript_commit_initial_kernel(seed_out: *mut u32, input: *const u32, input_len: u32)
);

/// Maximum number of input chunks the chunked transcript-commit kernel-arg
/// descriptor can hold. The pre-WHIR transcript pack feeds 5 chunks
/// (canonical-top-bits + external_challenges + setup cap + memory cap +
/// witness cap); 8 leaves headroom without any meaningful kernel-arg cost.
pub(crate) const GKR_CHUNKED_COMMIT_MAX_CHUNKS: usize = 8;

/// Kernel-arg descriptor for `transcript_commit_initial_chunked`. Streams
/// Blake2s over the logical concatenation of `num_chunks` device-resident
/// u32 buffers in one kernel launch (no host-side concat staging).
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct GpuChunkedInputDesc {
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

/// Gather `coset_count` cap regions, each `cap_words_per_coset` u32 words long, from the
/// device pointers in `src_ptrs` (each entry is a u64-encoded device pointer) into
/// `dst[0..coset_count*cap_words_per_coset]`. The caller orders `src_ptrs` to match the
/// desired output coset sequence (typically bit-reversed against the natural LDE order).
/// Replaces a per-coset `memory_copy_async` loop with one kernel launch.
///
/// Inline form of `gather_tree_caps`: the pointer table rides as kernel-arg
/// data (`__grid_constant__`), so callers (e.g. `TraceHolder::commit_all`)
/// avoid the H2D for a runtime pointer buffer.
pub(crate) fn gather_tree_caps_inline(
    src_ptrs: &[u64],
    dst: &mut DeviceSlice<u32>,
    cap_words_per_coset: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let coset_count = src_ptrs.len();
    assert!(coset_count > 0);
    assert!(cap_words_per_coset > 0);
    assert!(
        coset_count <= GKR_GATHER_TREE_CAPS_MAX_COSETS,
        "gather_tree_caps descriptor has {} cosets; exceeds GKR_GATHER_TREE_CAPS_MAX_COSETS = {}. \
         Raise the constant in ops/blake2s.rs (and the matching native constant) if a \
         future workload needs more.",
        coset_count,
        GKR_GATHER_TREE_CAPS_MAX_COSETS,
    );
    assert_eq!(
        dst.len(),
        coset_count * cap_words_per_coset as usize,
        "gather_tree_caps_inline dst length must match coset_count * cap_words_per_coset",
    );
    let mut desc = GpuGatherTreeCapsDesc::default();
    desc.coset_count = coset_count as u32;
    desc.cap_words_per_coset = cap_words_per_coset;
    desc.src_ptrs[..coset_count].copy_from_slice(src_ptrs);
    let threads_per_block = std::cmp::min(cap_words_per_coset, 256u32);
    let config = CudaLaunchConfig::basic(coset_count as u32, threads_per_block, stream);
    let args = GatherTreeCapsInlineArguments::new(desc, dst.as_mut_ptr());
    GatherTreeCapsInlineFunction::default().launch(&config, &args)
}

/// Gather `src_ptrs.len()` E4 evaluation regions (each `elements_per_addr`
/// E4 values long) from the device pointers in `src_ptrs` into the contiguous
/// `dst[0..src_ptrs.len()*elements_per_addr]`. The caller orders `src_ptrs`
/// (host slice) to match the desired output address sequence (typically the
/// BTreeMap key order of the per-layer transcript inputs). The pointer table
/// is passed by value as kernel-arg data; production callers must respect
/// `GKR_GATHER_MAX_ADDRESSES`.
pub(crate) fn gather_e_addresses(
    src_ptrs: &[u64],
    dst: &mut DeviceSlice<E4>,
    elements_per_addr: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let num_addresses = src_ptrs.len();
    assert!(num_addresses > 0);
    assert!(elements_per_addr > 0);
    assert!(
        num_addresses <= GKR_GATHER_MAX_ADDRESSES,
        "gather descriptor has {} addresses; exceeds GKR_GATHER_MAX_ADDRESSES = {}. \
         Raise the constant in gkr_address_audit.rs after re-running the audit.",
        num_addresses,
        GKR_GATHER_MAX_ADDRESSES,
    );
    assert_eq!(
        dst.len(),
        num_addresses * elements_per_addr as usize,
        "gather_e_addresses dst length must match num_addresses * elements_per_addr",
    );
    let mut desc = GpuGatherEAddressesDesc::default();
    desc.num_addresses = num_addresses as u32;
    desc.elements_per_addr = elements_per_addr;
    desc.src_ptrs[..num_addresses].copy_from_slice(src_ptrs);
    // Each E4 = 4 u32 words; cap thread count to a reasonable warp multiple.
    let words_per_addr = elements_per_addr.saturating_mul(4);
    let threads_per_block = std::cmp::min(words_per_addr, 64u32);
    let config = CudaLaunchConfig::basic(num_addresses as u32, threads_per_block, stream);
    let args = GatherEAddressesArguments::new(desc, dst.as_mut_ptr() as *mut u32);
    GatherEAddressesFunction::default().launch(&config, &args)
}

/// Chunked variant of [`transcript_commit_initial`]: computes
/// `seed = Blake2s(chunk_0 || chunk_1 || ... || chunk_{N-1})` from the IV without
/// requiring the host to first concatenate the chunks into a single contiguous
/// device buffer. `seed` must be exactly `STATE_SIZE` u32 words; written.
/// `chunks` are `(device pointer, u32 length)` pairs covering the logical
/// transcript prefix in order. Producing the same digest as the single-buffer
/// kernel is covered by `transcript_commit_initial_chunked_parity_*`.
pub(crate) fn transcript_commit_initial_chunked(
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
pub(crate) fn transcript_commit(
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
pub(crate) fn transcript_squeeze(
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
pub(crate) fn transcript_squeeze_e4(
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

pub(crate) fn blake2s_pow(
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
mod gkr_ops;

pub(crate) use gkr_ops::{
    assemble_query_indexes, backward_new_claims_linear, backward_new_claims_two_var,
    backward_sumcheck_round_update, build_combined_claim, whir_fold_round_update,
};

#[cfg(test)]
mod tests;
