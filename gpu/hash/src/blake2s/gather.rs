use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;

use super::{DG, STATE_SIZE};
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

/// Phase 3 (WHIR-on-device, GKR consolidation): gather base-field leaves for
/// all LDE cosets and all active oracles in one launch. The kernel handles the
/// coset filter internally and dispatches oracles via `gridDim.z`.
///
/// `descs[i]` for `i >= num_oracles` (and any active slot with
/// `columns_count == 0`) is skipped. `log_domain_size` is shared across all
/// active oracles (asserted upstream — see WHIR fold schedule). `cosets_ptr`
/// and `slab_dst_ptr` must point at valid device memory for the duration of
/// the call; this wrapper does not retain references.
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
    assert!(log_domain_size >= log_rows_per_leaf);
    let indexes_len = query_indexes.len();
    assert!(indexes_len <= u32::MAX as usize);
    let indexes_count = indexes_len as u32;
    // Assert unused desc slots are zeroed (defense against caller misuse).
    for i in (num_oracles as usize)..3 {
        assert_eq!(
            descs[i].cosets_ptr, 0,
            "inactive desc slot {i} must have cosets_ptr == 0"
        );
        assert_eq!(
            descs[i].columns_count, 0,
            "inactive desc slot {i} must have columns_count == 0"
        );
        assert_eq!(
            descs[i].slab_dst_ptr, 0,
            "inactive desc slot {i} must have slab_dst_ptr == 0"
        );
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
pub fn launch_gather_leaves_for_queries_from_ntt(
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
    assert!(log_packed_leaf_count + log_values_per_leaf <= trace_len.trailing_zeros());
    assert_eq!(
        trace_len,
        1u32 << (log_packed_leaf_count + log_values_per_leaf),
        "trace_len must equal packed_leaf_count * values_per_leaf"
    );
    let indexes_len = query_indexes.len();
    assert!(indexes_len <= u32::MAX as usize);
    let indexes_count = indexes_len as u32;
    let dst_cols = (1u32 << log_src_cols_per_coset) << log_values_per_leaf;
    assert!(slab_dst.len() >= indexes_len * (dst_cols as usize));
    // One thread per (query, col_in_leaf). Block dim x is a warp-multiple so
    // adjacent threads share the same col_in_leaf and read consecutive query
    // indexes (coalesced over `query_indexes`); the loaded `ntt_output` rows
    // depend on the q values so DRAM coalescing there is workload-dependent
    // (see spec §3.1 coalescing note).
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
        consolidated_tree: *const DG,
        log_leaves_count: u32,
        layers_count: u32,
        slab_dst: *mut u32,
    )
);

/// Phase 3 (WHIR-on-device, Step 3 consolidation): single-launch Full-tree
/// merkle-path gather across all LDE cosets for one oracle. The kernel
/// resolves the per-coset segment internally via `coset = q & lde_mask`.
///
/// The consolidated tree backing stores cosets in NATURAL order: coset `c`
/// occupies `consolidated_tree[c * stride_per_coset_in_digests ..
/// (c + 1) * stride_per_coset_in_digests]`. For Full mode,
/// `stride_per_coset_in_digests = 2 * leaves_count` (= `1 << (log_leaves_count
/// + 1)`), matching `TreesHolder::Full` indexing in
/// `prover/trace/holder/mod.rs`. `log_leaves_count` is per-coset (NOT whole
/// tree); the wrapper derives it from `stride_per_coset_in_digests`.
pub fn gather_merkle_paths_full_for_queries(
    query_indexes: &DeviceSlice<u32>,
    log_lde_factor: u32,
    stride_per_coset_in_digests: u32,
    consolidated_tree: &DeviceSlice<DG>,
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
    assert_eq!(WARP_SIZE % STATE_SIZE as u32, 0);
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
    pub slab_dst_ptr: u64,
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

/// Phase 3 (WHIR-on-device, GKR consolidation): single-launch Partial-tree
/// merkle-path gather across all LDE cosets and all active oracles.
///
/// For each query, the kernel hashes the first `LOG_WARP_SIZE` layers on the
/// fly from the per-oracle BF cosets backing (via warp-shuffle compression),
/// then walks the upper layers in the per-oracle partial-tree backing.
///
/// `descs[i]` for `i >= num_oracles` (and any active slot with
/// `columns_count == 0`) is skipped. `log_rows_per_leaf` and
/// `log_total_leaves_count` are shared across all active oracles (asserted
/// upstream — see WHIR fold schedule). The `cosets_ptr`, `partial_tree_ptr`,
/// and `slab_dst_ptr` fields must point at valid device memory for the
/// duration of the call; this wrapper does not retain references.
pub fn gather_merkle_paths_partial_for_queries(
    descs: &[OraclePartialPathDesc; 3],
    num_oracles: u32,
    log_lde_factor: u32,
    log_rows_per_leaf: u32,
    log_total_leaves_count: u32,
    stride_per_coset_in_digests: u32,
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
    let indexes_len = query_indexes.len();
    assert!(indexes_len <= u32::MAX as usize);
    let indexes_count = indexes_len as u32;
    // Per-coset partial-tree length in digests for `TreesHolder::Partial`:
    // `1 << (log_total_leaves_count + 1 - LOG_WARP_SIZE)`.
    let expected_stride = 1u32 << (log_total_leaves_count + 1 - LOG_WARP_SIZE);
    assert_eq!(
        stride_per_coset_in_digests, expected_stride,
        "stride_per_coset_in_digests ({stride_per_coset_in_digests}) must equal 1 << (log_total_leaves_count + 1 - LOG_WARP_SIZE) ({expected_stride})"
    );
    // Assert unused desc slots are zeroed (defense against caller misuse).
    for i in (num_oracles as usize)..3 {
        assert_eq!(
            descs[i].cosets_ptr, 0,
            "inactive desc slot {i} must have cosets_ptr == 0"
        );
        assert_eq!(
            descs[i].partial_tree_ptr, 0,
            "inactive desc slot {i} must have partial_tree_ptr == 0"
        );
        assert_eq!(
            descs[i].columns_count, 0,
            "inactive desc slot {i} must have columns_count == 0"
        );
        assert_eq!(
            descs[i].slab_dst_ptr, 0,
            "inactive desc slot {i} must have slab_dst_ptr == 0"
        );
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
/// this variant hard-codes single-oracle + single-TraceHolder-coset (WHIR
/// oracle's `log_lde_factor = 0`, `log_rows_per_leaf = 0`) and reads via the
/// pack-inverse used by `launch_gather_leaves_for_queries_from_ntt`.
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

cuda_kernel!(
    pub(crate) GatherTreeCaps,
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
pub const GKR_GATHER_TREE_CAPS_MAX_COSETS: usize = 32;

/// Kernel-arg descriptor for `gather_tree_caps_inline`. Consolidated form:
/// a single base pointer plus per-coset stride lets the kernel gather every
/// per-coset cap region from one contiguous tree backing. The kernel folds
/// the natural→bit-reversed coset reindex (`stage1_pos = bitreverse(
/// natural_idx, log_lde_factor)`) so the destination layout matches the
/// legacy stage1 ordering.
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct GpuGatherTreeCapsDesc {
    /// Number of source cosets to gather (= `1 << log_lde_factor`).
    pub coset_count: u32,
    /// Number of u32 words gathered per source coset.
    pub cap_words_per_coset: u32,
    /// Stride between per-coset segments in the source backing, in u32 words.
    /// The kernel reads `base_ptr + natural_idx * stride_per_coset_in_u32_words`
    /// for coset `natural_idx`.
    pub stride_per_coset_in_u32_words: u32,
    /// `log2(coset_count)`. Used to bit-reverse `natural_idx` into the
    /// destination cap-region slot.
    pub log_lde_factor: u32,
    /// Source backing base pointer treated as `const u32 *`.
    pub base_ptr: u64,
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

/// Maximum source addresses the `gather_e_addresses` kernel-arg descriptor can
/// hold. See `gkr_address_audit_helpers::GKR_GATHER_MAX_ADDRESSES` in
/// `circuit_prover` for the rationale; the audit panics if any future circuit
/// exceeds this.
pub const GKR_GATHER_MAX_ADDRESSES: usize = 1280;

/// Kernel-arg descriptor for `gather_e_addresses`. Inline form: passed by
/// value as `__grid_constant__` data.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct GpuGatherEAddressesDesc {
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

/// Gather `coset_count` cap regions, each `cap_words_per_coset` u32 words
/// long, from the consolidated tree backing pointed to by `base_ptr` into
/// `dst[0..coset_count * cap_words_per_coset]`. Per-coset source segments
/// are at stride `stride_per_coset_in_u32_words`. The kernel writes coset
/// `natural_idx` to `dst[bitreverse(natural_idx, log_lde_factor) * cap_words..]`
/// so the destination layout matches the legacy stage1 ordering used by
/// `read_per_coset_caps_synchronously`.
///
/// Inline form of `gather_tree_caps`: the descriptor rides as kernel-arg
/// data (`__grid_constant__`), so callers (e.g. `TraceHolder::commit_all`)
/// avoid an H2D for the source pointer table.
pub fn gather_tree_caps_inline(
    base_ptr: *const u32,
    coset_count: u32,
    cap_words_per_coset: u32,
    stride_per_coset_in_u32_words: u32,
    log_lde_factor: u32,
    dst: &mut DeviceSlice<u32>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(coset_count > 0);
    assert!(cap_words_per_coset > 0);
    assert!(stride_per_coset_in_u32_words >= cap_words_per_coset);
    assert_eq!(coset_count, 1u32 << log_lde_factor);
    assert!(
        (coset_count as usize) <= GKR_GATHER_TREE_CAPS_MAX_COSETS,
        "gather_tree_caps descriptor has {} cosets; exceeds GKR_GATHER_TREE_CAPS_MAX_COSETS = {}. \
         Raise the constant in ops/blake2s.rs (and the matching native constant) if a \
         future workload needs more.",
        coset_count,
        GKR_GATHER_TREE_CAPS_MAX_COSETS,
    );
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

/// Gather `src_ptrs.len()` E4 evaluation regions (each `elements_per_addr`
/// E4 values long) from the device pointers in `src_ptrs` into the contiguous
/// `dst[0..src_ptrs.len()*elements_per_addr]`. The caller orders `src_ptrs`
/// (host slice) to match the desired output address sequence (typically the
/// BTreeMap key order of the per-layer transcript inputs). The pointer table
/// is passed by value as kernel-arg data; production callers must respect
/// `GKR_GATHER_MAX_ADDRESSES`.
pub fn gather_e_addresses(
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
