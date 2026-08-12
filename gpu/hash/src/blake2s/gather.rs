//! Query-time gathering: leaf values, Merkle paths, and tree caps.
//!
//! The `*_for_queries` slab-write variants feed the proof slab's per-query
//! layout that `gpu_circuit_prover`'s proof parsing consumes:
//! - `query_indices` (`u32`): tree-space index per query.
//! - `query_leaves` (`BF`): row-major per query, `[v0c0, v0c1, ..., v(V-1)c(C-1)]`.
//! - `query_paths` (`u32`): query-major, `[layer0_d, layer1_d, ..., layer(L-1)_d]`
//!   per query, each digest is `STATE_SIZE` u32 words.
//!
//! The `#[doc(hidden)]` readers at the bottom are test-reference
//! implementations kept for downstream parity tests, not production paths.

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use super::{checked_u32, Digest, STATE_SIZE};
use gpu_core::primitives::device_structures::{
    DeviceMatrixChunkImpl, DeviceMatrixChunkMutImpl, MutPtrAndStride, PtrAndStride,
};
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::utils::{
    get_grid_block_dims_for_threads_count, LOG_WARP_SIZE, WARP_SIZE,
};

/// Kernel-arg descriptor for `gather_leaves_for_queries`. One entry per
/// base-field oracle: the consolidated cosets backing pointer, the per-oracle
/// column count, and the slab destination pointer. `columns_count == 0`
/// signals an inactive descriptor slot (the kernel skips the whole oracle).
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct OracleGatherDesc {
    /// `const BF*` consolidated cosets backing for this oracle. Coset `c`
    /// occupies elements `c * (columns_count << log_domain_size) ..
    /// (c + 1) * (columns_count << log_domain_size)`; within each coset the
    /// layout is column-major with stride `1 << log_domain_size`.
    pub cosets_ptr: u64,
    /// Number of base-field columns in this oracle. Set to `0` to mark the
    /// slot inactive — the kernel skips all writes for that oracle.
    pub columns_count: u32,
    /// Padding to keep the descriptor 8-byte aligned across language
    /// boundaries.
    pub _pad: u32,
    /// `BF*` slab destination for this oracle. Layout is query-major:
    /// `slab[q * (rows_per_leaf * columns_count) + v * columns_count + col]`.
    pub slab_dst_ptr: u64,
}

const _: () = {
    // Exact mirror of `gpu_oracle_gather_desc` in native/gather.cu — layout
    // drift silently breaks the by-value kernel ABI.
    assert!(std::mem::size_of::<OracleGatherDesc>() == 24);
};

impl OracleGatherDesc {
    /// Defense against caller misuse: unused desc slots must be zeroed.
    fn assert_inactive(&self, i: usize) {
        assert_eq!(
            self.cosets_ptr, 0,
            "inactive desc slot {i} must have cosets_ptr == 0"
        );
        assert_eq!(
            self.columns_count, 0,
            "inactive desc slot {i} must have columns_count == 0"
        );
        assert_eq!(
            self.slab_dst_ptr, 0,
            "inactive desc slot {i} must have slab_dst_ptr == 0"
        );
    }
}

cuda_kernel!(
    GatherLeavesForQueries,
    ab_gather_leaves_for_queries_kernel(
        num_oracles: u32,
        desc0: OracleGatherDesc,
        desc1: OracleGatherDesc,
        desc2: OracleGatherDesc,
        log_lde_factor: u32,
        log_domain_size: u32,
        log_rows_per_leaf: u32,
        query_indexes: *const u32,
        indexes_count: u32,
    )
);

/// Gather base-field leaves for
/// all LDE cosets and all active oracles in one launch. The kernel handles the
/// coset filter internally and dispatches oracles via `gridDim.z`.
///
/// `descs[i]` for `i >= num_oracles` (and any active slot with
/// `columns_count == 0`) is skipped. `log_domain_size` is shared across all
/// active oracles (the caller asserts this). `cosets_ptr`
/// and `slab_dst_ptr` must stay valid until the launched kernel completes on
/// `stream` (stream-ordered reclamation — freeing after this launch is
/// scheduled on the same stream — satisfies this); this wrapper does not
/// retain references.
pub fn gather_leaves_for_queries(
    descs: &[OracleGatherDesc; 3],
    num_oracles: u32,
    log_lde_factor: u32,
    log_domain_size: u32,
    log_rows_per_leaf: u32,
    query_indexes: &DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        num_oracles == 1 || num_oracles == 3,
        "gather_leaves_for_queries supports num_oracles in {{1, 3}}, got {num_oracles}"
    );
    // Kernel-side addressing shifts by these logs in u32.
    assert!(log_domain_size < 32);
    assert!(log_domain_size >= log_rows_per_leaf);
    let indexes_count = checked_u32(query_indexes.len());
    for (i, desc) in descs.iter().enumerate().skip(num_oracles as usize) {
        desc.assert_inactive(i);
    }
    // Max columns_count across the active descriptors. Must be >= 1 (the
    // launch needs a non-empty gridDim.y); zero-column oracles are skipped
    // by the kernel internally, but at least one active oracle must have
    // columns to do useful work.
    let max_cols = (0..num_oracles as usize)
        .map(|i| descs[i].columns_count)
        .max()
        .unwrap_or(0);
    assert!(
        max_cols >= 1,
        "gather_leaves_for_queries requires at least one active oracle with columns_count >= 1"
    );
    let rows_per_leaf = 1u32 << log_rows_per_leaf;
    let (mut grid_dim, block_dim) = if log_rows_per_leaf < LOG_WARP_SIZE {
        get_grid_block_dims_for_threads_count(
            1 << (LOG_WARP_SIZE - log_rows_per_leaf),
            indexes_count,
        )
    } else {
        (indexes_count.into(), 1.into())
    };
    let block_dim = (rows_per_leaf, block_dim.x);
    grid_dim.y = max_cols;
    let grid_dim = (grid_dim.x, grid_dim.y, num_oracles);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GatherLeavesForQueriesArguments::new(
        num_oracles,
        descs[0],
        descs[1],
        descs[2],
        log_lde_factor,
        log_domain_size,
        log_rows_per_leaf,
        query_indexes.as_ptr(),
        indexes_count,
    );
    GatherLeavesForQueriesFunction::default().launch(&config, &args)
}

cuda_kernel!(
    GatherLeavesForQueriesFromNtt,
    ab_gather_leaves_for_queries_from_ntt_kernel(
        ntt_output: *const BF,
        slab_dst: *mut BF,
        log_lde_factor: u32,
        log_packed_leaf_count: u32,
        log_values_per_leaf: u32,
        log_src_cols_per_coset: u32,
        trace_len: u32,
        query_indexes: *const u32,
        indexes_count: u32,
    )
);

/// WHIR oracle query-leaves gather against the natural multi-coset NTT
/// output. Single oracle, no multi-oracle descriptor indirection — the WHIR
/// recursive oracle is always queried alone.
///
/// `dst_slab` is written query-major: `dst_slab[idx * dst_cols + col]` where
/// `dst_cols = src_cols_per_coset << log_values_per_leaf = EXT4_DEGREE *
/// values_per_leaf`.
pub fn gather_leaves_for_queries_from_ntt(
    ntt_output: &DeviceSlice<BF>,
    slab_dst: &mut DeviceSlice<BF>,
    log_lde_factor: u32,
    log_packed_leaf_count: u32,
    log_values_per_leaf: u32,
    log_src_cols_per_coset: u32,
    trace_len: u32,
    query_indexes: &DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        log_lde_factor >= 1,
        "WHIR oracle requires log_lde_factor >= 1"
    );
    assert!(log_lde_factor + log_src_cols_per_coset < 32);
    assert!(log_packed_leaf_count + log_values_per_leaf <= trace_len.trailing_zeros());
    assert_eq!(
        trace_len,
        1u32 << (log_packed_leaf_count + log_values_per_leaf),
        "trace_len must equal packed_leaf_count * values_per_leaf"
    );
    // Queries can hit any natural coset, so the kernel may read the whole
    // consolidated NTT backing: trace_len rows x (lde_factor * src_cols) cols.
    let required_ntt_bf = (trace_len as usize) << (log_lde_factor + log_src_cols_per_coset);
    assert!(ntt_output.len() >= required_ntt_bf);
    let indexes_len = query_indexes.len();
    assert!(indexes_len <= u32::MAX as usize);
    let indexes_count = indexes_len as u32;
    let dst_cols = (1u32 << log_src_cols_per_coset) << log_values_per_leaf;
    assert!(
        dst_cols <= 65535,
        "dst_cols {dst_cols} exceeds the CUDA grid-Y limit"
    );
    assert!(slab_dst.len() >= indexes_len * (dst_cols as usize));
    // One thread per (query, col_in_leaf). Block dim x is a warp-multiple so
    // adjacent threads share the same col_in_leaf and read consecutive query
    // indexes (coalesced over `query_indexes`); the loaded `ntt_output` rows
    // depend on the q values so DRAM coalescing there is workload-dependent.
    let (grid_dim_query, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE, indexes_count);
    let grid_dim = (grid_dim_query.x, dst_cols, 1u32);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GatherLeavesForQueriesFromNttArguments::new(
        ntt_output.as_ptr(),
        slab_dst.as_mut_ptr(),
        log_lde_factor,
        log_packed_leaf_count,
        log_values_per_leaf,
        log_src_cols_per_coset,
        trace_len,
        query_indexes.as_ptr(),
        indexes_count,
    );
    GatherLeavesForQueriesFromNttFunction::default().launch(&config, &args)
}

cuda_kernel!(
    GatherMerklePathsFullForQueries,
    ab_gather_merkle_paths_full_for_queries_kernel(
        query_indexes: *const u32,
        indexes_count: u32,
        log_lde_factor: u32,
        stride_per_coset_in_digests: u32,
        consolidated_tree: *const Digest,
        log_leaves_count: u32,
        layers_count: u32,
        slab_dst: *mut u32,
    )
);

/// Single-launch Full-tree
/// merkle-path gather across all LDE cosets for one oracle. The kernel
/// resolves the per-coset segment internally via `coset = q & lde_mask`.
///
/// The consolidated tree backing stores cosets in NATURAL order: coset `c`
/// occupies `consolidated_tree[c * stride_per_coset_in_digests ..
/// (c + 1) * stride_per_coset_in_digests]`, where each per-coset slab is a
/// full tree: `stride_per_coset_in_digests = 2 * leaves_count`
/// (= `1 << (log_leaves_count + 1)`). `log_leaves_count` is per-coset (NOT
/// whole tree); the wrapper derives it from `stride_per_coset_in_digests`.
pub fn gather_merkle_paths_full_for_queries(
    query_indexes: &DeviceSlice<u32>,
    log_lde_factor: u32,
    stride_per_coset_in_digests: u32,
    consolidated_tree: &DeviceSlice<Digest>,
    slab_dst: &mut DeviceSlice<u32>,
    layers_count: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(query_indexes.len() <= u32::MAX as usize);
    let indexes_count = query_indexes.len() as u32;
    // stride_per_coset_in_digests == 2 * leaves_count for Full mode.
    assert!(
        stride_per_coset_in_digests >= 2 && stride_per_coset_in_digests.is_power_of_two(),
        "stride_per_coset_in_digests must be a power of two >= 2 (got {stride_per_coset_in_digests})"
    );
    let log_stride = stride_per_coset_in_digests.trailing_zeros();
    let log_leaves_count = log_stride - 1;
    assert!(layers_count <= log_leaves_count);
    let lde_factor = 1usize << log_lde_factor;
    assert_eq!(
        consolidated_tree.len(),
        lde_factor * stride_per_coset_in_digests as usize,
        "consolidated_tree length must equal lde_factor * stride_per_coset_in_digests"
    );
    // Kernel computes src_index in u32 (coset_offset + layer_offset + ...).
    // Guard against silent overflow.
    let total_u32_words =
        (lde_factor as u64) * (stride_per_coset_in_digests as u64) * (STATE_SIZE as u64);
    assert!(
        total_u32_words <= u32::MAX as u64,
        "consolidated tree u32-word footprint ({total_u32_words}) exceeds u32::MAX; kernel would overflow"
    );
    assert_eq!(
        slab_dst.len(),
        query_indexes.len() * layers_count as usize * STATE_SIZE
    );
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(WARP_SIZE / STATE_SIZE as u32, indexes_count);
    let grid_dim = (grid_dim.x, layers_count);
    let block_dim = (STATE_SIZE as u32, block_dim.x);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GatherMerklePathsFullForQueriesArguments::new(
        query_indexes.as_ptr(),
        indexes_count,
        log_lde_factor,
        stride_per_coset_in_digests,
        consolidated_tree.as_ptr(),
        log_leaves_count,
        layers_count,
        slab_dst.as_mut_ptr(),
    );
    GatherMerklePathsFullForQueriesFunction::default().launch(&config, &args)
}

/// Kernel-arg descriptor for `gather_merkle_paths_partial_for_queries`. One
/// entry per base-field oracle: the consolidated cosets backing pointer (for
/// on-the-fly bottom-layer hashing), the consolidated partial-tree backing
/// pointer (for upper-layer walks), the per-oracle column count, and the slab
/// destination pointer. `columns_count == 0` signals an inactive descriptor
/// slot (the kernel skips the whole oracle).
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct OraclePartialPathDesc {
    /// `const BF*` consolidated cosets backing for this oracle. Coset `c`
    /// occupies elements `c * (columns_count << log_domain_size) ..
    /// (c + 1) * (columns_count << log_domain_size)`; within each coset the
    /// layout is column-major with stride `1 << log_domain_size`.
    pub cosets_ptr: u64,
    /// `const u32*` consolidated partial-tree backing for this oracle.
    /// Coset `c` occupies digest words `c * stride_per_coset_in_digests *
    /// STATE_SIZE .. (c + 1) * stride_per_coset_in_digests * STATE_SIZE`.
    pub partial_tree_ptr: u64,
    /// Number of base-field columns in this oracle. Set to `0` to mark the
    /// slot inactive — the kernel skips all writes for that oracle.
    pub columns_count: u32,
    /// Padding to keep the descriptor 8-byte aligned across language
    /// boundaries.
    pub _pad: u32,
    /// `u32*` slab destination for this oracle. Layout is query-major:
    /// `slab[q * layers_count * STATE_SIZE + layer * STATE_SIZE + word]`.
    /// Must be 32-byte aligned (the bottom path layers are digest stores).
    pub slab_dst_ptr: u64,
}

const _: () = {
    // Exact mirror of `gpu_oracle_partial_path_desc` in native/gather.cu —
    // layout drift silently breaks the by-value kernel ABI.
    assert!(std::mem::size_of::<OraclePartialPathDesc>() == 32);
};

impl OraclePartialPathDesc {
    /// Defense against caller misuse: unused desc slots must be zeroed.
    fn assert_inactive(&self, i: usize) {
        assert_eq!(
            self.cosets_ptr, 0,
            "inactive desc slot {i} must have cosets_ptr == 0"
        );
        assert_eq!(
            self.partial_tree_ptr, 0,
            "inactive desc slot {i} must have partial_tree_ptr == 0"
        );
        assert_eq!(
            self.columns_count, 0,
            "inactive desc slot {i} must have columns_count == 0"
        );
        assert_eq!(
            self.slab_dst_ptr, 0,
            "inactive desc slot {i} must have slab_dst_ptr == 0"
        );
    }
}

cuda_kernel!(
    GatherMerklePathsPartialForQueries,
    ab_gather_merkle_paths_partial_for_queries_kernel(
        num_oracles: u32,
        desc0: OraclePartialPathDesc,
        desc1: OraclePartialPathDesc,
        desc2: OraclePartialPathDesc,
        log_lde_factor: u32,
        log_rows_per_leaf: u32,
        log_total_leaves_count: u32,
        stride_per_coset_in_digests: u32,
        layers_count: u32,
        query_indexes: *const u32,
        indexes_count: u32,
    )
);

/// Single-launch Partial-tree
/// merkle-path gather across all LDE cosets and all active oracles.
///
/// For each query, the kernel hashes the first `LOG_WARP_SIZE` layers on the
/// fly from the per-oracle BF cosets backing (via warp-shuffle compression),
/// then walks the upper layers in the per-oracle partial-tree backing.
///
/// `descs[i]` for `i >= num_oracles` (and any active slot with
/// `columns_count == 0`) is skipped. `log_rows_per_leaf` and
/// `log_total_leaves_count` are shared across all active oracles (the caller
/// asserts this). The `cosets_ptr`, `partial_tree_ptr`,
/// and `slab_dst_ptr` fields must stay valid until the launched kernel
/// completes on `stream` (stream-ordered reclamation satisfies this); this
/// wrapper does not retain references.
pub fn gather_merkle_paths_partial_for_queries(
    descs: &[OraclePartialPathDesc; 3],
    num_oracles: u32,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_total_leaves_count: u32,
    layers_count: u32,
    query_indexes: &DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        num_oracles == 1 || num_oracles == 3,
        "gather_merkle_paths_partial_for_queries supports num_oracles in {{1, 3}}, got {num_oracles}"
    );
    assert!(layers_count >= LOG_WARP_SIZE);
    assert!(log_total_leaves_count >= LOG_WARP_SIZE);
    // The upper-tree walk starts at log_total_leaves_count - LOG_WARP_SIZE
    // digests and halves per layer; deeper requests would underflow past the
    // per-coset root and read outside the partial tree.
    assert!(layers_count <= log_total_leaves_count);
    let indexes_count = checked_u32(query_indexes.len());
    // Per-coset partial-tree slab length in digests: the full pyramid above
    // the LOG_WARP_SIZE warp-hashed bottom layers.
    let stride_per_coset_in_digests = 1u32 << (log_total_leaves_count + 1 - LOG_WARP_SIZE);
    for (i, desc) in descs.iter().enumerate() {
        if i >= num_oracles as usize {
            desc.assert_inactive(i);
        } else if desc.columns_count != 0 {
            // The bottom path layers are written as 32-byte digest stores.
            assert_eq!(
                desc.slab_dst_ptr % 32,
                0,
                "oracle {i} slab_dst_ptr must be 32-byte aligned"
            );
        }
    }
    let grid_dim = (indexes_count, num_oracles);
    let block_dim = WARP_SIZE;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GatherMerklePathsPartialForQueriesArguments::new(
        num_oracles,
        descs[0],
        descs[1],
        descs[2],
        log_lde_factor,
        log_rows_per_leaf,
        log_total_leaves_count,
        stride_per_coset_in_digests,
        layers_count,
        query_indexes.as_ptr(),
        indexes_count,
    );
    GatherMerklePathsPartialForQueriesFunction::default().launch(&config, &args)
}

cuda_kernel!(
    GatherMerklePathsPartialForQueriesFromNtt,
    ab_gather_merkle_paths_partial_for_queries_from_ntt_kernel(
        ntt_output: *const BF,
        partial_tree: *const u32,
        slab_dst: *mut u32,
        natural_log_lde_factor: u32,
        log_values_per_leaf: u32,
        log_src_cols_per_coset: u32,
        log_packed_leaf_count: u32,
        trace_len: u32,
        log_total_leaves_count: u32,
        layers_count: u32,
        query_indexes: *const u32,
        indexes_count: u32,
    )
);

/// Single-oracle WHIR Partial-tree merkle-path gather against the natural
/// multi-coset NTT cosets backing. The packed-layout sibling
/// (`gather_merkle_paths_partial_for_queries`) is parameterized to support
/// three GKR oracles and reads its cosets backing with packed-leaf addressing;
/// this variant hard-codes single-oracle + single-packed-coset (the WHIR
/// oracle's tree has `log_lde_factor = 0`, `log_rows_per_leaf = 0`) and reads via the
/// pack-inverse used by `gather_leaves_for_queries_from_ntt`.
pub fn gather_merkle_paths_partial_for_queries_from_ntt(
    ntt_output: &DeviceSlice<BF>,
    partial_tree: &DeviceSlice<u32>,
    slab_dst: &mut DeviceSlice<u32>,
    natural_log_lde_factor: u32,
    log_values_per_leaf: u32,
    log_src_cols_per_coset: u32,
    log_packed_leaf_count: u32,
    trace_len: u32,
    log_total_leaves_count: u32,
    layers_count: u32,
    query_indexes: &DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(layers_count >= LOG_WARP_SIZE);
    assert!(log_total_leaves_count >= LOG_WARP_SIZE);
    // The upper-tree walk starts at log_total_leaves_count - LOG_WARP_SIZE
    // digests and halves per layer; deeper requests would underflow past the
    // root and read outside the partial tree.
    assert!(layers_count <= log_total_leaves_count);
    assert_eq!(
        log_total_leaves_count,
        log_packed_leaf_count + natural_log_lde_factor,
        "log_total_leaves_count must equal log_packed_leaf_count + natural_log_lde_factor"
    );
    assert_eq!(
        trace_len,
        1u32 << (log_packed_leaf_count + log_values_per_leaf),
        "trace_len must equal packed_leaf_count * values_per_leaf"
    );
    // Queries can hit any natural coset, so the kernel may read the whole
    // consolidated NTT backing.
    assert!(natural_log_lde_factor + log_src_cols_per_coset < 32);
    let required_ntt_bf = (trace_len as usize) << (natural_log_lde_factor + log_src_cols_per_coset);
    assert!(ntt_output.len() >= required_ntt_bf);
    // Full partial-tree pyramid slab, in u32 words.
    let required_partial_tree =
        (1usize << (log_total_leaves_count + 1 - LOG_WARP_SIZE)) * STATE_SIZE;
    assert!(partial_tree.len() >= required_partial_tree);
    // The bottom path layers are written as 32-byte digest stores.
    assert_eq!(slab_dst.as_ptr() as usize % 32, 0);
    let indexes_len = query_indexes.len();
    assert!(indexes_len <= u32::MAX as usize);
    let indexes_count = indexes_len as u32;
    assert!(slab_dst.len() >= indexes_len * (layers_count as usize) * STATE_SIZE);
    let grid_dim = (indexes_count, 1, 1);
    let block_dim = WARP_SIZE;
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = GatherMerklePathsPartialForQueriesFromNttArguments::new(
        ntt_output.as_ptr(),
        partial_tree.as_ptr(),
        slab_dst.as_mut_ptr(),
        natural_log_lde_factor,
        log_values_per_leaf,
        log_src_cols_per_coset,
        log_packed_leaf_count,
        trace_len,
        log_total_leaves_count,
        layers_count,
        query_indexes.as_ptr(),
        indexes_count,
    );
    GatherMerklePathsPartialForQueriesFromNttFunction::default().launch(&config, &args)
}

/// Kernel-arg descriptor for `gather_tree_caps_inline`. Consolidated form:
/// a single base pointer plus per-coset stride lets the kernel gather every
/// per-coset cap region from one contiguous tree backing. The kernel folds
/// the natural→bit-reversed coset reindex so the destination is in
/// bit-reversed coset order — the cap order downstream readers expect.
#[repr(C)]
#[derive(Clone, Copy, Default)]
struct GpuGatherTreeCapsDesc {
    /// Number of source cosets to gather (= `1 << log_lde_factor`).
    coset_count: u32,
    /// Number of u32 words gathered per source coset.
    cap_words_per_coset: u32,
    /// Stride between per-coset segments in the source backing, in u32 words.
    /// The kernel reads `base_ptr + natural_idx * stride_per_coset_in_u32_words`
    /// for coset `natural_idx`.
    stride_per_coset_in_u32_words: u32,
    /// `log2(coset_count)`. Used to bit-reverse `natural_idx` into the
    /// destination cap-region slot.
    log_lde_factor: u32,
    /// Source backing base pointer treated as `const u32 *`.
    base_ptr: u64,
}

const _: () = {
    // Exact mirror of `gpu_gather_tree_caps_desc` in native/gather.cu.
    assert!(std::mem::size_of::<GpuGatherTreeCapsDesc>() == 24);
    assert!(
        std::mem::size_of::<GpuGatherTreeCapsDesc>() <= 32 * 1024,
        "GpuGatherTreeCapsDesc must fit under the 32 KB inline kernel-arg ceiling"
    );
};

cuda_kernel!(
    GatherTreeCapsInline,
    ab_gather_tree_caps_inline_kernel(desc: GpuGatherTreeCapsDesc, dst: *mut u32)
);

/// Maximum source addresses the `gather_e_addresses` kernel-arg descriptor can
/// hold. Must match `GKR_GATHER_MAX_ADDRESSES` in `native/gather.cu`.
const GKR_GATHER_MAX_ADDRESSES: usize = 1280;

/// Kernel-arg descriptor for `gather_e_addresses`. Inline form: passed by
/// value as `__grid_constant__` data.
#[repr(C)]
#[derive(Clone, Copy)]
struct GpuGatherEAddressesDesc {
    /// Number of populated entries in `src_ptrs`.
    num_addresses: u32,
    /// Number of E4 elements gathered per source address.
    elements_per_addr: u32,
    /// Source device pointers (one per address). Each is treated as a
    /// `const u32 *` referring to `elements_per_addr * 4` u32 words.
    src_ptrs: [u64; GKR_GATHER_MAX_ADDRESSES],
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
    // Exact mirror of `gpu_gather_e_addresses_desc` in native/gather.cu.
    assert!(std::mem::size_of::<GpuGatherEAddressesDesc>() == 8 + 8 * GKR_GATHER_MAX_ADDRESSES);
    assert!(
        std::mem::size_of::<GpuGatherEAddressesDesc>() <= 32 * 1024,
        "GpuGatherEAddressesDesc must fit under the 32 KB inline kernel-arg ceiling"
    );
};

cuda_kernel!(
    GatherEAddresses,
    ab_gather_e_addresses_kernel(desc: GpuGatherEAddressesDesc, dst: *mut u32)
);

/// Gather `coset_count` cap regions, each `cap_words_per_coset` u32 words
/// long, from the consolidated tree backing pointed to by `base_ptr` into
/// `dst[0..coset_count * cap_words_per_coset]`. Per-coset source segments
/// are at stride `stride_per_coset_in_u32_words`. The kernel writes coset
/// `natural_idx` to `dst[bitreverse(natural_idx, log_lde_factor) * cap_words..]`
/// — the bit-reversed cap order downstream readers expect.
///
/// The descriptor rides as kernel-arg data (`__grid_constant__`), so callers
/// avoid an H2D for the source pointer table.
/// `base_ptr` must stay valid until the launched kernel completes on `stream`
/// (stream-ordered reclamation satisfies this).
pub fn gather_tree_caps_inline(
    base_ptr: *const u32,
    cap_words_per_coset: u32,
    stride_per_coset_in_u32_words: u32,
    log_lde_factor: u32,
    dst: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(log_lde_factor < 32);
    let coset_count = 1u32 << log_lde_factor;
    assert!(cap_words_per_coset > 0);
    assert!(stride_per_coset_in_u32_words >= cap_words_per_coset);
    assert_eq!(
        dst.len(),
        (coset_count as usize) * (cap_words_per_coset as usize),
        "gather_tree_caps_inline dst length must match coset_count * cap_words_per_coset",
    );
    let desc = GpuGatherTreeCapsDesc {
        coset_count,
        cap_words_per_coset,
        stride_per_coset_in_u32_words,
        log_lde_factor,
        base_ptr: base_ptr as u64,
    };
    let threads_per_block = std::cmp::min(cap_words_per_coset, 256u32);
    let config = CudaLaunchConfig::basic(coset_count, threads_per_block, stream);
    let args = GatherTreeCapsInlineArguments::new(desc, dst.as_mut_ptr());
    GatherTreeCapsInlineFunction::default().launch(&config, &args)
}

/// Gather `src_ptrs.len()` equal-size E4 evaluation regions from the device
/// pointers in `src_ptrs` into the contiguous `dst`. The per-address element
/// count is derived as `dst.len() / src_ptrs.len()`. The caller orders
/// `src_ptrs` (host slice) to match the desired output address sequence
/// (typically the BTreeMap key order of the per-layer transcript inputs). The
/// pointer table is passed by value as kernel-arg data; the pointed-to
/// allocations must stay valid until the launched kernel completes on
/// `stream` (stream-ordered reclamation satisfies this). Production callers
/// must respect `GKR_GATHER_MAX_ADDRESSES`.
pub fn gather_e_addresses(
    src_ptrs: &[u64],
    dst: &mut DeviceSlice<E4>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let num_addresses = src_ptrs.len();
    assert!(num_addresses > 0);
    assert!(
        num_addresses <= GKR_GATHER_MAX_ADDRESSES,
        "gather descriptor has {} addresses; exceeds GKR_GATHER_MAX_ADDRESSES = {}",
        num_addresses,
        GKR_GATHER_MAX_ADDRESSES,
    );
    assert_eq!(
        dst.len() % num_addresses,
        0,
        "gather_e_addresses dst length ({}) must be a multiple of num_addresses ({num_addresses})",
        dst.len(),
    );
    let elements_per_addr = (dst.len() / num_addresses) as u32;
    assert!(elements_per_addr > 0);
    let mut desc = GpuGatherEAddressesDesc {
        num_addresses: num_addresses as u32,
        elements_per_addr,
        ..Default::default()
    };
    desc.src_ptrs[..num_addresses].copy_from_slice(src_ptrs);
    // Each E4 = 4 u32 words; cap thread count to a reasonable warp multiple.
    let words_per_addr = elements_per_addr.saturating_mul(4);
    let threads_per_block = std::cmp::min(words_per_addr, 64u32);
    let config = CudaLaunchConfig::basic(num_addresses as u32, threads_per_block, stream);
    let args = GatherEAddressesArguments::new(desc, dst.as_mut_ptr() as *mut u32);
    GatherEAddressesFunction::default().launch(&config, &args)
}

cuda_kernel!(
    QueryIndexToTreeIndex,
    ab_query_index_to_tree_index_kernel(
        d_query_indexes: *const u32,
        d_out: *mut u32,
        indexes_count: u32,
        log_lde_factor: u32,
        coset_tree_size_log2: u32,
    )
);

/// Map raw query indexes to the tree-space indexes the verifier's
/// `BaseFieldQuery.index` expects:
/// `bitreverse(q & (lde - 1), log_lde) << coset_tree_size_log2 | q >> log_lde`.
pub fn query_index_to_tree_index(
    d_query_indexes: &DeviceSlice<u32>,
    d_out: &mut DeviceSlice<u32>,
    log_lde_factor: u32,
    coset_tree_size_log2: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    // The kernel composes `bitrev(coset) << coset_tree_size_log2 | internal`
    // in u32; a wider domain would silently truncate the tree index.
    assert!(log_lde_factor + coset_tree_size_log2 <= 32);
    let n = d_query_indexes.len();
    assert_eq!(d_out.len(), n);
    let n = checked_u32(n);
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE, n);
    let config = CudaLaunchConfig::basic(grid_dim, block_dim, stream);
    let args = QueryIndexToTreeIndexArguments::new(
        d_query_indexes.as_ptr(),
        d_out.as_mut_ptr(),
        n,
        log_lde_factor,
        coset_tree_size_log2,
    );
    QueryIndexToTreeIndexFunction::default().launch(&config, &args)
}

// ---------------------------------------------------------------------------
// Test-reference readers. No production callers: these direct gathers from a
// fully-materialized cosets/tree backing back circuit_prover's TraceHolder
// cache-mode and whir/fold query parity tests (which validate the production
// tree-construction paths against independent CPU ground truth). `pub` +
// `#[doc(hidden)]` because a dependency's `#[cfg(test)]` items are invisible
// to consumers.
// ---------------------------------------------------------------------------

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

#[doc(hidden)]
pub fn gather_leaf_rows(
    indexes: &DeviceSlice<u32>,
    bit_reverse_indexes: bool,
    log_rows_per_leaf: u32,
    values: &(impl DeviceMatrixChunkImpl<BF> + ?Sized),
    result: &mut (impl DeviceMatrixChunkMutImpl<BF> + ?Sized),
    stream: &CudaStream,
) -> CudaResult<()> {
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
    assert_eq!(result_rows, indexes.len() << log_rows_per_leaf);
    let indexes_count = checked_u32(indexes.len());
    let (mut grid_dim, block_dim) = if log_rows_per_leaf < LOG_WARP_SIZE {
        get_grid_block_dims_for_threads_count(
            1 << (LOG_WARP_SIZE - log_rows_per_leaf),
            indexes_count,
        )
    } else {
        (indexes_count.into(), 1.into())
    };
    let block_dim = (rows_per_leaf, block_dim.x);
    grid_dim.y = checked_u32(result_cols);
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
        values: *const Digest,
        log_leaves_count: u32,
        results: *mut Digest,
    )
);

#[doc(hidden)]
pub fn gather_merkle_paths_device(
    indexes: &DeviceSlice<u32>,
    values: &DeviceSlice<Digest>,
    results: &mut DeviceSlice<Digest>,
    layers_count: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    let indexes_count = checked_u32(indexes.len());
    let values_count = values.len();
    assert!(values_count.is_power_of_two());
    let log_values_count = values_count.trailing_zeros();
    assert_ne!(log_values_count, 0);
    let log_leaves_count = log_values_count - 1;
    // A per-coset cap of size 1 means the query path spans the full coset subtree depth.
    assert!(layers_count <= log_leaves_count);
    assert_eq!(indexes.len() * layers_count as usize, results.len());
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

#[doc(hidden)]
pub fn gather_merkle_paths_from_rows(
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
    let values_len = values.len();
    assert_eq!(values_len % cols_count, 0);
    let rows_count = values_len / cols_count;
    assert!(rows_count.is_power_of_two());
    let log_rows_count = rows_count.trailing_zeros();
    assert!(log_rows_count >= log_rows_per_leaf);
    let indexes_count = checked_u32(indexes.len());
    assert!(layers_count >= LOG_WARP_SIZE);
    assert_eq!(indexes.len() * layers_count as usize, merkle_paths.len());
    let cols_count = checked_u32(cols_count);
    let log_total_leaves_count = log_rows_count - log_rows_per_leaf;
    assert!(layers_count <= log_total_leaves_count);
    // Full partial-tree pyramid (in digests) backing the upper-layer walk.
    assert!(tree_bottom.len() >= 1usize << (log_total_leaves_count + 1 - LOG_WARP_SIZE));
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
